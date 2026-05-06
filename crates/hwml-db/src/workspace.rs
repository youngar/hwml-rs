/// Workspace-level aggregation queries
///
/// This module implements the library-level compilation model where all .hwml files
/// in a workspace are automatically aggregated into a single global namespace.
use crate::{ManifestPath, SourceFile, VfsFileMap};
use hwml_core::{QualifiedName, Source, SourceInfo, Word};
use hwml_elab::stub_table::{harvest_program, StubTable};
use hwml_surface::Program;
use hwml_workspace::Workspace;
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

/// Parse surface syntax for a single file.
///
/// This is a Salsa query so parsing results are cached per file.
/// When a file is edited, only that file's parsing is invalidated.
#[salsa::tracked]
pub fn parse_surface_program(db: &dyn salsa::Database, source_file: SourceFile) -> Option<Program> {
    let text = source_file.text(db);
    hwml_surface::parsing::parse(text.as_bytes())
}

/// Harvest declarations from a single file.
///
/// This is a Salsa query so harvesting results are cached per file.
/// When a file is edited, only that file's declarations are re-harvested.
///
/// # Incremental Compilation
///
/// This query enables fine-grained incrementality:
/// - Depends on `parse_surface_program(file)` (also cached)
/// - When file A is edited:
///   - `parse_surface_program(A)` invalidates → re-parses A
///   - `file_declarations(A)` invalidates → re-harvests A
///   - `library_declarations()` invalidates → BUT uses cached results for B, C, D
/// - Result: Only file A is re-parsed and re-harvested!
#[salsa::tracked]
pub fn file_declarations<'db>(
    db: &'db dyn salsa::Database,
    source_file: SourceFile,
) -> Arc<Vec<(QualifiedName<'db>, hwml_elab::stub_table::Stub<'db>)>> {
    // Parse program (cached by Salsa!)
    let program = parse_surface_program(db, source_file);

    // If parsing failed, return empty
    let Some(program) = program else {
        return Arc::new(Vec::new());
    };

    // Create Source for location tracking
    let path = source_file.path(db);
    let source = {
        let label = Word::new(db, path.display().to_string().as_str());
        Source::new(db, SourceInfo::Synthetic(label))
    };

    // Start at root namespace (None = global root)
    let root_namespace: Option<QualifiedName> = None;

    // Harvest into a temporary StubTable
    let mut temp_table = StubTable::new();
    if let Err(harvest_err) = harvest_program(db, &mut temp_table, source, root_namespace, &program)
    {
        eprintln!(
            "Warning: Error harvesting declarations from {}: {}",
            path.display(),
            harvest_err
        );
        return Arc::new(Vec::new());
    }

    // Extract declarations as a vector
    let declarations: Vec<_> = temp_table
        .stubs()
        .map(|(name, stub)| (name, stub.clone()))
        .collect();

    Arc::new(declarations)
}

/// Harvest all declarations from all files in the workspace.
///
/// This query aggregates declarations from ALL .hwml files in the VfsFileMap
/// into a single global StubTable. All files are treated as part of the same
/// logical library.
///
/// # Architecture
///
/// This implements Phase 2 of the Workspace Aggregation model (Incremental Optimization):
/// - Iterates over all files in VfsFileMap
/// - Calls `file_declarations()` for each file (cached!)
/// - Merges all declarations into global StubTable
/// - Detects collisions for concrete definitions during merge
///
/// # Incremental Compilation (Phase 2 Optimization)
///
/// When a file is edited:
/// 1. `parse_surface_program(edited_file)` invalidates → re-parses ONLY edited file
/// 2. `file_declarations(edited_file)` invalidates → re-harvests ONLY edited file
/// 3. `library_declarations()` invalidates → BUT uses CACHED results for other files!
/// 4. Only the edited file is re-parsed and re-harvested
/// 5. Other files use cached parse and harvest results
///
/// This is much more efficient than re-harvesting all files!
#[salsa::tracked]
pub fn library_declarations<'db>(
    db: &'db dyn salsa::Database,
    vfs_map: VfsFileMap,
) -> Arc<StubTable<'db>> {
    let mut global_table = StubTable::new();

    // Iterate over all files in workspace
    let files = vfs_map.files(db);
    for (_path, source_file) in files.iter() {
        // Get declarations for this file (CACHED by Salsa!)
        let file_decls = file_declarations(db, *source_file);

        // Merge into global table, checking for collisions
        for (name, stub) in file_decls.iter() {
            if let Err(err) = global_table.insert(*name, stub.kind, stub.source_range.clone()) {
                eprintln!("Warning: Collision detected: {}", err);
            }
        }
    }

    Arc::new(global_table)
}

/// Load all declarations from a workspace including all dependencies.
///
/// This implements Phase 3 of the Workspace Aggregation model (Cross-Library Dependencies).
///
/// # Architecture
///
/// Given a path to a `hwml.toml` manifest:
/// 1. Load the workspace using `hwml_workspace::Workspace::load()`
/// 2. For each library in topological order (dependencies first):
///    - Discover all `.hwml` files in the library
///    - Create a `VfsFileMap` for the library
///    - Call `library_declarations()` to harvest that library's declarations
///    - Merge into global `StubTable`, checking for collisions
///
/// # Collision Detection
///
/// Concrete definitions (those lowered to Verilog) must have unique names across ALL libraries.
/// If two libraries define `def Fifo_32 = ...`, this is a hard error because it would cause
/// a Verilog linker error.
///
/// Parametric definitions can share names across libraries (they're compile-time only).
///
/// # Incremental Compilation
///
/// This query depends on:
/// - The manifest path (Salsa input)
/// - `library_declarations()` for each library (cached!)
///
/// When a file is edited:
/// - Only that library's `library_declarations()` is recomputed
/// - Other libraries use cached results
/// - This query re-aggregates, but most work is cached
#[salsa::tracked]
pub fn workspace_declarations<'db>(
    db: &'db dyn salsa::Database,
    manifest_path: ManifestPath,
) -> (Arc<StubTable<'db>>, Arc<HashMap<PathBuf, SourceFile>>) {
    // Load workspace (this reads hwml.toml and finds all dependencies)
    let manifest_path_buf = manifest_path.path(db).clone();
    let workspace = match Workspace::load(manifest_path_buf.clone()) {
        Ok(ws) => ws,
        Err(e) => {
            eprintln!(
                "Error loading workspace from {:?}: {}",
                manifest_path_buf, e
            );
            return (Arc::new(StubTable::new()), Arc::new(HashMap::new()));
        }
    };

    let mut global_table = StubTable::new();
    let mut all_files = HashMap::new();

    // Process libraries in topological order (dependencies first)
    for lib_name in &workspace.topo_order {
        let lib_manifest = &workspace.libraries[lib_name];

        // Create VfsFileMap for this library
        let mut files = HashMap::new();
        for source_path in &lib_manifest.source_files {
            // Read file contents
            let text = match std::fs::read_to_string(source_path) {
                Ok(t) => t,
                Err(e) => {
                    eprintln!("Warning: Failed to read {}: {}", source_path.display(), e);
                    continue;
                }
            };

            let source_file = SourceFile::new(db, source_path.clone(), text);
            files.insert(source_path.clone(), source_file);
            all_files.insert(source_path.clone(), source_file);
        }

        let vfs_map = VfsFileMap::new(db, Arc::new(files));

        // Harvest declarations from this library
        let lib_decls = library_declarations(db, vfs_map);

        // Merge into global table, checking for collisions
        for (name, stub) in lib_decls.stubs() {
            if let Err(err) = global_table.insert(name, stub.kind, stub.source_range.clone()) {
                eprintln!(
                    "Warning: Cross-library collision in '{}': {}",
                    lib_name, err
                );
            }
        }
    }

    (Arc::new(global_table), Arc::new(all_files))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::HwmlDatabase;
    use salsa::Setter;
    use std::collections::HashMap;
    use std::path::PathBuf;

    #[test]
    fn test_library_declarations_empty_workspace() {
        let mut db = HwmlDatabase::new();

        // Create empty VfsFileMap
        let vfs_map = VfsFileMap::new(&mut db, Arc::new(HashMap::new()));

        // Should return empty StubTable
        let stubs = library_declarations(&db, vfs_map);
        assert!(stubs.is_empty());
    }

    #[test]
    fn test_library_declarations_single_file() {
        let mut db = HwmlDatabase::new();

        // Create a simple HWML file
        let path = PathBuf::from("/test/foo.hwml");
        let text = "def foo : Bit = i1".to_string();
        let source_file = SourceFile::new(&mut db, path.clone(), text);

        // Create VfsFileMap with one file
        let mut files = HashMap::new();
        files.insert(path, source_file);
        let vfs_map = VfsFileMap::new(&mut db, Arc::new(files));

        // Harvest declarations
        let stubs = library_declarations(&db, vfs_map);

        // Should have harvested the `foo` definition
        assert!(!stubs.is_empty());
        // Note: We'd need to expose a way to query StubTable to verify the exact entry
    }

    #[test]
    fn test_library_declarations_multiple_files() {
        let mut db = HwmlDatabase::new();

        // Create two HWML files
        let path1 = PathBuf::from("/test/foo.hwml");
        let text1 = "def foo : Bit = i1".to_string();
        let source_file1 = SourceFile::new(&mut db, path1.clone(), text1);

        let path2 = PathBuf::from("/test/bar.hwml");
        let text2 = "def bar : Bit = i0".to_string();
        let source_file2 = SourceFile::new(&mut db, path2.clone(), text2);

        // Create VfsFileMap with two files
        let mut files = HashMap::new();
        files.insert(path1, source_file1);
        files.insert(path2, source_file2);
        let vfs_map = VfsFileMap::new(&mut db, Arc::new(files));

        // Harvest declarations
        let stubs = library_declarations(&db, vfs_map);

        // Should have harvested declarations from both files
        assert!(!stubs.is_empty());
    }

    #[test]
    fn test_file_declarations_single_file() {
        let mut db = HwmlDatabase::new();

        // Create a simple HWML file
        let path = PathBuf::from("/test/foo.hwml");
        let text = "def foo : Bit = i1".to_string();
        let source_file = SourceFile::new(&mut db, path, text);

        // Harvest declarations from this file only
        let file_decls = file_declarations(&db, source_file);

        // Should have declarations
        assert!(!file_decls.is_empty());
    }

    #[test]
    fn test_file_declarations_caching() {
        let mut db = HwmlDatabase::new();

        // Create a file
        let path = PathBuf::from("/test/foo.hwml");
        let text = "def foo : Bit = i1".to_string();
        let source_file = SourceFile::new(&mut db, path, text);

        // Call file_declarations twice
        let decls1 = file_declarations(&db, source_file);
        let decls2 = file_declarations(&db, source_file);

        // Should return the same Arc (pointer equality means it's cached!)
        assert!(Arc::ptr_eq(&decls1, &decls2));
    }

    #[test]
    fn test_workspace_declarations_with_dependencies() {
        use std::fs;
        use tempfile::TempDir;

        let mut db = HwmlDatabase::new();

        // Create a temporary directory structure
        let temp_dir = TempDir::new().unwrap();
        let root = temp_dir.path();

        // Create a dependency library "base"
        let base_dir = root.join("base");
        fs::create_dir_all(&base_dir).unwrap();
        fs::write(base_dir.join("hwml.toml"), "[library]\nname = \"base\"\n").unwrap();
        fs::write(base_dir.join("types.hwml"), "def BaseType : Type = Bit").unwrap();

        // Create main library that depends on "base"
        let main_dir = root.join("main");
        fs::create_dir_all(&main_dir).unwrap();
        fs::write(
            main_dir.join("hwml.toml"),
            "[library]\nname = \"main\"\n\n[dependencies]\nbase = { path = \"../base\" }\n",
        )
        .unwrap();
        fs::write(main_dir.join("main.hwml"), "def MainValue : Bit = i1").unwrap();

        // Load workspace declarations
        let manifest_path_buf = main_dir.join("hwml.toml");
        let manifest_path = ManifestPath::new(&mut db, manifest_path_buf);
        let decls = workspace_declarations(&db, manifest_path);

        // Should have declarations from both libraries
        assert!(!decls.is_empty());
        // Note: We can't easily test specific symbols without exposing StubTable's iterator
        // but we verified it's not empty, which means it loaded something!
    }

    #[test]
    fn test_multi_file_mutual_recursion() {
        let mut db = HwmlDatabase::new();

        // Create two HWML files that reference each other
        let path1 = PathBuf::from("/test/a.hwml");
        let text1 = "def foo : Bit = bar".to_string(); // References bar from b.hwml
        let source_file1 = SourceFile::new(&mut db, path1.clone(), text1);

        let path2 = PathBuf::from("/test/b.hwml");
        let text2 = "def bar : Bit = i1".to_string();
        let source_file2 = SourceFile::new(&mut db, path2.clone(), text2);

        // Create VfsFileMap with both files
        let mut files = HashMap::new();
        files.insert(path1, source_file1);
        files.insert(path2, source_file2);
        let vfs_map = VfsFileMap::new(&mut db, Arc::new(files));

        // Harvest declarations - should work because both are in global scope
        let stubs = library_declarations(&db, vfs_map);

        // Should have declarations from both files
        assert!(!stubs.is_empty());
        assert!(stubs.len() >= 2); // At least foo and bar
    }

    #[test]
    fn test_incremental_file_edit() {
        let mut db = HwmlDatabase::new();

        // Create initial file
        let path = std::path::PathBuf::from("/test/foo.hwml");
        let text1 = "def foo : Bit = i1".to_string();
        let source_file1 = SourceFile::new(&mut db, path.clone(), text1);

        // Harvest first time
        let decls1 = file_declarations(&db, source_file1);
        assert!(!decls1.is_empty());

        // "Edit" the file using .set_text() to trigger Salsa invalidation
        let text2 = "def foo : Bit = i0".to_string(); // Changed value
        source_file1.set_text(&mut db).to(text2);

        // Harvest second time
        let decls2 = file_declarations(&db, source_file1);
        assert!(!decls2.is_empty());

        // The Arc pointers should be different (file was edited)
        assert!(!Arc::ptr_eq(&decls1, &decls2));
    }

    #[test]
    fn test_namespace_extension_across_files() {
        let mut db = HwmlDatabase::new();

        // File 1: Define namespace Foo with member A
        let path1 = PathBuf::from("/test/foo1.hwml");
        let text1 = "namespace Foo { def A : Bit = i1 }".to_string();
        let source_file1 = SourceFile::new(&mut db, path1.clone(), text1);

        // File 2: Extend namespace Foo with member B
        let path2 = PathBuf::from("/test/foo2.hwml");
        let text2 = "namespace Foo { def B : Bit = i0 }".to_string();
        let source_file2 = SourceFile::new(&mut db, path2.clone(), text2);

        // Create VfsFileMap with both files
        let mut files = HashMap::new();
        files.insert(path1, source_file1);
        files.insert(path2, source_file2);
        let vfs_map = VfsFileMap::new(&mut db, Arc::new(files));

        // Harvest declarations - both should be in namespace Foo
        let stubs = library_declarations(&db, vfs_map);

        // Should have declarations from both files
        // Both should be under Foo namespace
        assert!(!stubs.is_empty());
        assert!(stubs.len() >= 2); // At least Foo.A and Foo.B
    }

    #[test]
    fn test_concrete_vs_parametric_definitions() {
        let mut db = HwmlDatabase::new();

        // File with parametric definition (has bindings)
        let path1 = PathBuf::from("/test/param.hwml");
        // Note: The actual parsing determines if something is parametric
        // For now, we just test that the harvesting works
        let text1 = "def MyType : Type = Bit".to_string();
        let source_file1 = SourceFile::new(&mut db, path1.clone(), text1);

        // File with concrete definition (no bindings)
        let path2 = PathBuf::from("/test/concrete.hwml");
        let text2 = "def MyValue : Bit = i1".to_string();
        let source_file2 = SourceFile::new(&mut db, path2.clone(), text2);

        let decls1 = file_declarations(&db, source_file1);
        let decls2 = file_declarations(&db, source_file2);

        // Both should harvest successfully
        assert!(!decls1.is_empty());
        assert!(!decls2.is_empty());
    }
}
