# ADR-011: Module Resolution and File Discovery

**Status:** Approved ✅
**Date:** 2026-05-03
**Deciders:** Core team
**Related:** [[ADR-007-salsa-driven-compilation]], [[ADR-008-vfs-abstraction]], [[ADR-006-multi-layer-build-configuration]]

**⚠️ CRITICAL:** This ADR includes three essential implementation gotchas (path normalization, early cutoff, recursive tree walking). Read the entire ADR before implementing!

---

## Context

HWML needs to resolve module references in two contexts:

1. **Cross-library dependencies:** `open Fifo` (references external library)
2. **Intra-library modules:** `module Registers from "registers.hwml"` (internal organization)

**Design choice:** HWML uses **explicit module declarations** in source code rather than implicit filesystem mapping (unlike Java/Go). This decouples logical module namespace from physical file structure, allowing refactoring freedom.

**Syntax (strawman - subject to refinement):**
```hwml
// Cross-library import (from hwml.toml manifest)
open Fifo  // Imports library's public interface

// Intra-library module declaration
module Registers from "registers.hwml"  // Relative to current file
module State from "state/machine.hwml"  // Can use subdirectories

// Re-export for library interface
export def makeUart = ...
export type UartConfig = ...
```

**The trap:** Module resolution CANNOT access `CompilerSession` or VFS from inside a `#[salsa::tracked]` query. Queries are pure functions with only `&dyn Db` access.

**The question:** How do we structure module resolution as a pure Salsa query while handling file discovery and missing file detection?

---

## Decision

**HWML uses explicit module declarations in source code, not implicit filesystem mapping.**

### The Hybrid Module System

**1. Cross-Library Dependencies (Manifest-Based)**

Libraries are declared in `hwml.toml` manifests:

```toml
# lib/uart/hwml.toml
[package]
name = "uart"
version = "0.1.0"

[dependencies]
fifo = { path = "../fifo" }
axi = { path = "../axi" }

[lib]
root = "src/lib.hwml"  # Library entry point
```

When you write `open Fifo`, the compiler:
1. Reads workspace manifests (Salsa query)
2. Finds `fifo` library manifest
3. Loads the library's root file (`lib/fifo/src/lib.hwml`)
4. Elaborates it to get exported declarations

**2. Intra-Library Modules (Source-Based)**

Within a library, modules are declared explicitly in source:

```hwml
// lib/uart/src/lib.hwml

// Internal modules (implementation detail)
module Registers from "registers.hwml"
module StateMachine from "state_machine.hwml"

// Public interface
export def makeUart (config : UartConfig) : Module = ...
export type UartConfig = { baudRate : Nat, ... }
```

When the parser sees `module Registers from "registers.hwml"`, the compiler:
1. Resolves path relative to current file's directory
2. Looks up file in `VfsFileMap` input
3. Parses and elaborates that file
4. Makes declarations available in current scope

### The Input Architecture

**Input 1: Individual Source Files**
```rust
#[salsa::input]
pub struct SourceFile {
    #[return_ref]
    pub path: PathBuf,

    #[return_ref]
    pub text: String,
}
```

**Input 2: VFS File Map (All Known Files)**
```rust
#[salsa::input]
pub struct VfsFileMap {
    /// Map of canonical path → SourceFile
    /// Updated whenever files are added/removed by CompilerSession
    #[return_ref]
    pub files: Arc<HashMap<PathBuf, SourceFile>>,
}
```

### Initialization Flow

```rust
impl CompilerSession {
    pub fn new_for_workspace(workspace_root: PathBuf) -> Result<Self> {
        let mut session = Self::new_with_os_vfs();
        
        // 1. Discover all .hwml files in workspace (filesystem scan)
        let discovered_files = Self::discover_hwml_files(&workspace_root)?;
        
        // 2. Create Salsa SourceFile inputs for each
        let mut file_map = HashMap::new();
        for path in discovered_files {
            let text = std::fs::read_to_string(&path)?;
            let source_file = SourceFile::new(&mut session.db, path.clone(), text);
            file_map.insert(path, source_file);
        }
        
        // 3. Create VfsFileMap input (snapshot of workspace)
        let vfs_file_map = VfsFileMap::new(&mut session.db, Arc::new(file_map));
        session.vfs_file_map = Some(vfs_file_map);
        
        Ok(session)
    }
    
    fn discover_hwml_files(root: &Path) -> Result<Vec<PathBuf>> {
        // Use walkdir or similar to find all *.hwml files
        let mut files = Vec::new();
        for entry in walkdir::WalkDir::new(root) {
            let entry = entry?;
            if entry.path().extension() == Some("hwml".as_ref()) {
                files.push(entry.path().canonicalize()?);
            }
        }
        Ok(files)
    }
}
```

### The Module Tree Query (With Early Cutoff Optimization) ⚡

**⚠️ CRITICAL PERFORMANCE TRAP:** If `library_module_tree` directly depends on `parse_file()`, then **every keystroke invalidates the entire module tree**, defeating incremental compilation!

**The Solution: Structural Extraction + Early Cutoff**

We insert an intermediate query that **only** extracts module declarations, ignoring function bodies and type definitions:

```rust
/// Extract only the structural imports/module declarations from a file
/// This enables Salsa's "Early Cutoff" optimization
#[derive(Debug, Clone, PartialEq, Eq, Hash)]  // ← CRITICAL: Eq for early cutoff!
pub struct FileImports {
    /// Module declarations: (module_name, relative_path)
    pub modules: Vec<(String, PathBuf)>,
}

#[salsa::tracked]
pub fn file_imports(db: &dyn Db, file: SourceFile) -> FileImports {
    let ast = parse_file(db, file);

    // Walk AST, but ONLY extract module declarations
    // Throw away function bodies, type definitions, etc.
    let mut modules = Vec::new();

    for decl in ast.top_level_declarations() {
        match decl {
            Decl::ModuleDecl { name, file_path } => {
                modules.push((name.clone(), PathBuf::from(file_path)));
            }
            _ => {} // Ignore functions, types, etc.
        }
    }

    FileImports { modules }
}
```

**Now `library_module_tree` depends on `file_imports`, not `parse_file`:**

```rust
/// Builds the module tree for a library
/// Uses file_imports() for early cutoff optimization
#[salsa::tracked]
pub fn library_module_tree(
    db: &dyn Db,
    vfs_map: VfsFileMap,
    library: LibraryId,
) -> Result<ModuleTree, ModuleResolutionError> {
    let root_file = library.root_file(db);

    // Depends on file_imports, NOT parse_file!
    let imports = file_imports(db, root_file);

    let mut tree = ModuleTree::new();

    for (module_name, relative_path) in imports.modules {
        // Resolve path relative to root file's directory
        let resolved_path = root_file.path(db)
            .parent()
            .unwrap()
            .join(&relative_path);

        // Look up in VFS (pure lookup, no IO!)
        match vfs_map.files(db).get(&resolved_path) {
            Some(&source_file) => {
                tree.insert(module_name.clone(), source_file);

                // Recursively process submodule imports
                // Note: This is safe because HWML modules form a tree (no cycles)
                // Use helper function to avoid query self-recursion
                collect_submodule_tree(db, vfs_map, source_file, &mut tree);
            }
            None => {
                tree.add_error(ModuleResolutionError::FileNotFound {
                    module: module_name,
                    expected_path: resolved_path,
                });
            }
        }
    }

    Ok(tree)
}

/// Data structure holding the module tree
pub struct ModuleTree {
    /// Map of module name → SourceFile
    modules: HashMap<String, SourceFile>,

    /// Resolution errors (missing files, etc.)
    errors: Vec<ModuleResolutionError>,
}

/// Helper function to recursively collect submodule trees
/// This is a regular function, not a Salsa query, to avoid self-recursion issues
fn collect_submodule_tree(
    db: &dyn Db,
    vfs_map: VfsFileMap,
    file: SourceFile,
    tree: &mut ModuleTree,
) {
    let imports = file_imports(db, file);

    for (module_name, relative_path) in imports.modules {
        let resolved_path = file.path(db).parent().unwrap().join(&relative_path);

        match vfs_map.files(db).get(&resolved_path) {
            Some(&source_file) => {
                tree.insert(module_name.clone(), source_file);
                // Recurse into submodules (safe because modules form a tree)
                collect_submodule_tree(db, vfs_map, source_file, tree);
            }
            None => {
                tree.add_error(ModuleResolutionError::FileNotFound {
                    module: module_name,
                    expected_path: resolved_path,
                });
            }
        }
    }
}
```

**The Magic of Early Cutoff:**

```
User types in function body of registers.hwml:
    ↓
parse_file(registers.hwml) invalidated, re-runs
    ↓
file_imports(registers.hwml) invalidated, re-runs
    ↓
Salsa compares new FileImports to old FileImports
    ↓
FileImports are Eq (module declarations unchanged!)
    ↓
🔥 EARLY CUTOFF: Salsa stops here!
    ↓
library_module_tree() NOT invalidated (uses cached result)
    ↓
name_resolution() NOT invalidated
    ↓
typecheck_library() NOT invalidated
    ↓
✨ LSP responds in 1ms, only re-typechecks the single changed function
```

### Cross-Library Resolution

```rust
/// Resolve a cross-library import like `open Fifo`
#[salsa::tracked]
pub fn resolve_library_import(
    db: &dyn Db,
    workspace: WorkspaceRoot,
    library_name: String,
) -> Result<LibraryInterface, Error> {
    // 1. Get workspace manifests
    let libs = workspace_libraries(db, workspace);

    // 2. Find the library
    let lib_manifest = libs.get(&library_name)
        .ok_or(Error::LibraryNotFound)?;

    // 3. Elaborate the library (recursive Salsa query from ADR-007)
    library_interface(db, workspace, library_name)
}
```

**Both queries are pure:** All inputs tracked by Salsa, no IO or VFS access.

---

## Handling Missing Files

**Question:** What happens when a user types `open Std.Vector` but `vector.hwml` doesn't exist yet?

**Answer: The FileSet is updated via file watcher, triggering Salsa invalidation.**

### File Watcher Integration

```rust
impl CompilerSession {
    /// Called by file watcher when files are created/deleted
    pub fn on_file_system_changed(&mut self, event: FileSystemEvent) {
        match event {
            FileSystemEvent::Created(path) if path.extension() == Some("hwml".as_ref()) => {
                self.add_file_to_workspace(path);
            }
            FileSystemEvent::Deleted(path) => {
                self.remove_file_from_workspace(path);
            }
            _ => {}
        }
    }
    
    fn add_file_to_workspace(&mut self, path: PathBuf, text: String) {
        // 1. Create Salsa SourceFile input
        let source_file = SourceFile::new(&mut self.db, path.clone(), text);

        // 2. Update VfsFileMap (THIS INVALIDATES SALSA QUERIES!)
        let mut files = (*self.vfs_file_map.unwrap().files(&self.db)).clone();
        files.insert(path, source_file);
        self.vfs_file_map.unwrap().set_files(&mut self.db).to(Arc::new(files));
    }

    fn remove_file_from_workspace(&mut self, path: PathBuf) {
        let mut files = (*self.vfs_file_map.unwrap().files(&self.db)).clone();
        files.remove(&path);
        self.vfs_file_map.unwrap().set_files(&mut self.db).to(Arc::new(files));
    }
}
```

**Flow for Missing Files:**

```hwml
// lib/uart/src/lib.hwml
module Registers from "registers.hwml"  // ← File doesn't exist yet!
```

1. `library_module_tree` query runs
2. Parses `module Registers from "registers.hwml"`
3. Resolves path: `lib/uart/src/registers.hwml`
4. Looks up in `VfsFileMap` → **file not found**
5. Records error in `ModuleTree.errors`
6. Compiler shows: "Module file not found: registers.hwml"

**When user creates the file:**

7. User creates `lib/uart/src/registers.hwml` and saves
8. File watcher detects creation → calls `session.add_file_to_workspace(path, text)`
9. `add_file_to_workspace` updates `VfsFileMap` input
10. **Salsa automatically invalidates** `library_module_tree` query
11. Query re-runs, finds file this time, no error!
12. Red squiggly disappears in editor ✨

---

## Rationale

### 1. Explicit Module Declarations Decouple Logic from Filesystem

**Implicit filesystem mapping (Java/Go style):**
```
// In Go/Java: import path.to.Vector
// MUST correspond to: path/to/Vector.java or path/to/vector.go
```

**Problems:**
- Refactoring file structure breaks all imports
- File naming conventions enforced (case sensitivity issues across platforms)
- Tooling must scan filesystem to discover modules

**Explicit module declarations (HWML/Rust/OCaml style):**
```hwml
// In source: module Registers from "internal/regs.hwml"
// Consumers only see: Uart.Registers
// File can be moved/renamed without breaking consumers
```

**Benefits:**
- **Refactoring freedom:** Move `internal/regs.hwml` → `impl/registers.hwml`, change one line in `lib.hwml`
- **Encapsulation:** Internal file structure is implementation detail
- **Cross-platform:** No case-sensitivity issues (module names are case-sensitive, filenames may not be)
- **Versioning:** Can change file organization between library versions without breaking API

**Example refactoring:**
```hwml
// Version 1.0 of library:
module Uart from "uart.hwml"

// Version 2.0 (split into multiple files):
module Uart from "uart/controller.hwml"
// Consumers' `open Uart` still works!
```

### 2. Module Tree Query Elegantly Handles Missing Files

**The traditional problem:** How does module resolution know when a missing file appears?

**With explicit declarations + VfsFileMap input:**

```hwml
module Registers from "registers.hwml"  // Declared in source
```

1. `library_module_tree` query parses this declaration
2. Looks up `registers.hwml` in `VfsFileMap`
3. **If missing:** Records error in `ModuleTree.errors`, shows diagnostic
4. **When file created:** CompilerSession updates `VfsFileMap` input
5. **Salsa invalidates** `library_module_tree` (because input changed)
6. Query re-runs, finds file, error disappears

**No polling, no special "check for missing files" logic needed.** Salsa's dependency tracking handles everything.

### 3. Pure Module Resolution (The Core Benefit)

**Without VfsFileMap input (broken):**
```rust
#[salsa::tracked]
pub fn library_module_tree(db: &dyn Db, ...) -> Result<ModuleTree> {
    let ast = parse_file(db, root_file);

    for module_decl in ast.modules() {
        let path = compute_path(module_decl.file_path);
        session.load_file(&path)  // ❌ COMPILER ERROR: no `session` in scope!
    }
}
```

**With VfsFileMap input (correct):**
```rust
#[salsa::tracked]
pub fn library_module_tree(db: &dyn Db, vfs_map: VfsFileMap, ...) -> Result<ModuleTree> {
    let ast = parse_file(db, root_file);

    for module_decl in ast.modules() {
        let path = compute_path(module_decl.file_path);
        vfs_map.files(db).get(&path)  // ✅ Pure lookup, fully tracked
    }
}
```

Salsa can cache and invalidate properly because all inputs are explicit.

### 4. Early Cutoff Optimization Prevents Invalidation Cascades ⚡ **CRITICAL**

**The Performance Trap (Naive Implementation):**

If `library_module_tree` directly depends on `parse_file()`:

```rust
// ❌ NAIVE (causes performance disaster)
#[salsa::tracked]
pub fn library_module_tree(...) -> ModuleTree {
    let ast = parse_file(db, root_file);  // Direct dependency!
    extract_modules(&ast)
}
```

**What happens when user types in a function body:**

```
User types `let x = 42;` in registers.hwml
    ↓
SourceFile.text changed → parse_file(registers) invalidated
    ↓
library_module_tree depends on parse_file → INVALIDATED
    ↓
name_resolution depends on library_module_tree → INVALIDATED
    ↓
typecheck_file depends on name_resolution → INVALIDATED
    ↓
🔥 ENTIRE LIBRARY RE-TYPECHECKED ON EVERY KEYSTROKE
    ↓
LSP freezes for 500ms+, terrible UX
```

**The Fix: Structural Extraction Query**

Insert `file_imports()` query that returns `#[derive(Eq)]` struct:

```rust
// ✅ CORRECT (enables early cutoff)
#[salsa::tracked]
pub fn file_imports(db: &dyn Db, file: SourceFile) -> FileImports {
    let ast = parse_file(db, file);
    // Extract ONLY module declarations, ignore everything else
    FileImports { modules: extract_module_decls(&ast) }
}

#[salsa::tracked]
pub fn library_module_tree(...) -> ModuleTree {
    let imports = file_imports(db, root_file);  // Depends on imports, not AST!
    build_tree(imports)
}
```

**What happens with early cutoff:**

```
User types `let x = 42;` in registers.hwml
    ↓
SourceFile.text changed → parse_file(registers) invalidated
    ↓
file_imports(registers) invalidated, re-runs
    ↓
Extracts module declarations (unchanged!)
    ↓
Returns same FileImports as before
    ↓
Salsa compares: old_imports == new_imports ✓
    ↓
🔥 EARLY CUTOFF: library_module_tree NOT invalidated!
    ↓
name_resolution NOT invalidated
    ↓
typecheck_file invalidated ONLY for registers.hwml (single file)
    ↓
✨ LSP responds in <10ms
```

**Why `#[derive(Eq)]` is critical:**

Salsa needs to **compare** the old and new query results to decide if downstream queries should re-run. Without `Eq`, Salsa assumes the result changed and invalidates everything.

**This is the exact pattern used by rust-analyzer** to achieve sub-millisecond incremental compilation in massive codebases.

### 5. File Discovery Happens Once (Efficient)

**Eager discovery at initialization:**
- Filesystem scan happens once when `CompilerSession` is created
- All `.hwml` files registered as Salsa inputs upfront
- Subsequent module resolution is pure lookup (fast)

**Incremental updates via file watcher:**
- File created → Add to FileSet → Salsa invalidates
- File deleted → Remove from FileSet → Salsa invalidates
- File modified → Update SourceFile.text → Salsa invalidates

**No redundant scanning:** We don't re-scan the filesystem on every module resolution.

### 6. Hermetic CLI Builds (Buck2 Compatible)

For CLI builds, the initial file discovery creates an atomic snapshot:

```rust
// CLI main.rs
let session = CompilerSession::new_for_workspace(workspace_root)?;
// ↑ All files loaded into Salsa inputs NOW
// Even if files change on disk mid-compilation, Salsa uses the snapshot
```

This is critical for remote execution and deterministic builds.

### 7. LSP Gets Live Updates

For LSP, the file watcher ensures live updates:

```rust
// LSP server
let mut session = CompilerSession::new_for_workspace(workspace_root)?;

// Start file watcher
let (tx, rx) = channel();
let watcher = notify::watcher(tx, Duration::from_secs(1))?;
watcher.watch(&workspace_root, RecursiveMode::Recursive)?;

loop {
    select! {
        recv(rx) -> event => {
            session.on_file_system_changed(event.unwrap());
        }
        recv(lsp_events) -> msg => {
            handle_lsp_message(&mut session, msg);
        }
    }
}
```

User creates file → Watcher fires → FileSet updated → Diagnostics refresh automatically.

### 8. Matches rust-analyzer Architecture

rust-analyzer uses **exactly this pattern**:

**1. Structural Extraction for Early Cutoff:**
```rust
// rust-analyzer/crates/hir-def/src/item_tree.rs
#[salsa::tracked]
pub fn file_item_tree(db: &dyn DefDatabase, file_id: FileId) -> Arc<ItemTree> {
    let syntax = db.parse(file_id).tree();

    // Extract ONLY top-level items (structs, functions, modules)
    // Ignore function bodies, expressions, etc.
    let item_tree = ItemTree::from_syntax(&syntax);
    Arc::new(item_tree)
}
```

**2. VfsFileMap / SourceRoot:**
```rust
// rust-analyzer/crates/base-db/src/input.rs
#[salsa::input]
pub struct SourceRoot {
    // Map of file paths to file IDs
}
```

**3. Module Resolution via Item Tree:**
```rust
// rust-analyzer/crates/hir-def/src/nameres.rs
#[salsa::tracked]
pub fn crate_def_map(db: &dyn DefDatabase, krate: CrateId) -> Arc<CrateDefMap> {
    // Depends on file_item_tree(), NOT parse()!
    // Achieves early cutoff when function bodies change
}
```

Our architecture **directly mirrors** rust-analyzer's proven design:
- `file_imports()` ≈ `file_item_tree()` (structural extraction)
- `VfsFileMap` ≈ `SourceRoot` (file registry)
- `library_module_tree()` ≈ `crate_def_map()` (module resolution)

---

## Consequences

### Positive

1. **Module resolution is pure:** No IO, no VFS access, fully cacheable
2. **Salsa invalidation works correctly:** FileSet is an input, changes tracked automatically
3. **Efficient:** File discovery once at init, then pure lookups
4. **Hermetic CLI builds:** Snapshot at initialization prevents races
5. **LSP gets live updates:** File watcher updates FileSet, Salsa recomputes

### Negative

1. **Eagerly scans entire workspace:** Could be slow for very large workspaces
   - *Mitigation:* Most HWML projects will be <1000 files. Scanning takes <100ms.
   - *Future optimization:* Lazy loading per library if needed.

2. **File watcher complexity:** Need to integrate `notify` crate or similar
   - *Mitigation:* Well-understood pattern, used by all modern LSPs.

3. **FileSet clones on update:** Updating FileSet clones the HashMap
   - *Mitigation:* Use `Arc<HashMap>` inside FileSet, cheap to clone.

### Neutral

- **Missing files are errors, not lazy loads:** This is by design. HWML doesn't support "create file on import" like some languages.

---

## Alternatives Considered

### Alternative 1: Lazy File Loading

**What:** Don't eagerly scan workspace. Load files on-demand when module resolution asks for them.

```rust
#[salsa::tracked]
pub fn resolve_module_path(...) -> Result<SourceFile> {
    let path = compute_path();

    // Try to load lazily
    if let Some(file) = try_load_from_cache(db, &path) {
        return Ok(file);
    }

    // ❌ PROBLEM: Can't do IO here! We're in a pure query!
    let text = std::fs::read_to_string(&path)?;  // ← Not allowed
    Ok(SourceFile::new(db, path, text))
}
```

**Why rejected:** Cannot do IO from inside Salsa query. Violates purity.

### Alternative 2: Return PathBuf, Separate Lookup

**What:** Module resolution returns `PathBuf`, separate query looks up `SourceFile`:

```rust
#[salsa::tracked]
pub fn resolve_module_path(...) -> Result<PathBuf> {
    Ok(compute_path())  // Pure path computation
}

#[salsa::tracked]
pub fn source_file_for_path(db: &dyn Db, path: PathBuf) -> Option<SourceFile> {
    // ❌ PROBLEM: Still need FileSet to do pure lookup!
    // Can't load from disk here.
}
```

**Why rejected:** Still requires FileSet input to avoid IO in query. Doesn't simplify anything.

### Alternative 3: Module Resolution Outside Salsa

**What:** Module resolution happens in `CompilerSession`, not in Salsa query:

```rust
impl CompilerSession {
    pub fn resolve_and_elaborate_import(&mut self, module_path: &[String]) -> Result<()> {
        let path = self.compute_path(module_path);
        let file = self.vfs.get_or_create_file(&mut self.db, &path);
        elaborate_file(&self.db, file)?;
        Ok(())
    }
}
```

**Why rejected:**
- Breaks Salsa's demand-driven model
- Can't cache module resolution
- Requires manual dependency tracking

---

## Implementation

### Path Normalization (Critical for Correctness) 🚨

**The Trap:** `VfsFileMap` uses `PathBuf` as HashMap keys. **Any mismatch breaks lookup:**

```rust
// ❌ BROKEN: Different representations of same path
files.insert(PathBuf::from("lib/uart/src/uart.hwml"), file1);  // Relative
files.get(&PathBuf::from("/abs/path/lib/uart/src/uart.hwml"))  // Absolute → None!

// ❌ BROKEN: Case sensitivity differences (Windows)
files.insert(PathBuf::from("C:\\project\\lib.hwml"), file);
files.get(&PathBuf::from("c:\\project\\lib.hwml"))  // Lowercase drive → None!
```

**The Fix: Strict Canonicalization Boundary**

```rust
impl CompilerSession {
    /// Normalize path to canonical absolute form
    /// ALWAYS call this before VfsFileMap operations!
    fn normalize_path(&self, path: &Path) -> Result<PathBuf> {
        // 1. Canonicalize (resolves symlinks, makes absolute)
        let canonical = path.canonicalize()
            .or_else(|_| {
                // File might not exist yet, manually make absolute
                std::env::current_dir()?.join(path)
            })?;

        // 2. On Windows, normalize drive letter case
        #[cfg(windows)]
        let canonical = normalize_windows_path(canonical);

        Ok(canonical)
    }

    /// LSP integration: Convert URI to normalized path
    fn uri_to_path(&self, uri: &lsp_types::Url) -> Result<PathBuf> {
        let path = uri.to_file_path()
            .map_err(|_| Error::InvalidUri)?;
        self.normalize_path(&path)
    }

    pub fn add_file_to_workspace(&mut self, path: PathBuf, text: String) {
        // ALWAYS normalize before inserting!
        let canonical = self.normalize_path(&path).unwrap();

        let source_file = SourceFile::new(&mut self.db, canonical.clone(), text);

        let mut files = (*self.vfs_file_map.unwrap().files(&self.db)).clone();
        files.insert(canonical, source_file);
        self.vfs_file_map.unwrap().set_files(&mut self.db).to(Arc::new(files));
    }
}

#[cfg(windows)]
fn normalize_windows_path(path: PathBuf) -> PathBuf {
    // Ensure drive letter is uppercase: C:\ not c:\
    let s = path.to_string_lossy();
    if s.len() >= 2 && s.chars().nth(1) == Some(':') {
        let mut chars = s.chars();
        let drive = chars.next().unwrap().to_ascii_uppercase();
        PathBuf::from(format!("{}{}", drive, &s[1..]))
    } else {
        path
    }
}
```

**LSP Integration Example:**

```rust
impl LanguageServer {
    fn on_did_change(&mut self, params: DidChangeTextDocumentParams) {
        // URI from LSP: file:///C:/project/lib.hwml
        let path = self.session.uri_to_path(&params.text_document.uri).unwrap();
        // path is now: C:\project\lib.hwml (normalized)

        self.session.update_file(&path, params.content_changes[0].text.clone());
        // VfsFileMap lookup will succeed!
    }
}
```

### VfsFileMap with Arc for Cheap Cloning

```rust
#[salsa::input]
pub struct VfsFileMap {
    #[return_ref]
    pub files: Arc<HashMap<PathBuf, SourceFile>>,
}

impl CompilerSession {
    fn add_file_to_workspace(&mut self, path: PathBuf, text: String) {
        let canonical = self.normalize_path(&path).unwrap();
        let source_file = SourceFile::new(&mut self.db, canonical.clone(), text);

        // Arc makes this clone cheap (just increment refcount)
        let mut files = (*self.vfs_file_map.unwrap().files(&self.db)).clone();
        files.insert(canonical, source_file);

        self.vfs_file_map.unwrap().set_files(&mut self.db).to(Arc::new(files));
    }
}
```

### File Watcher Integration (LSP)

```rust
use notify::{Watcher, RecursiveMode, watcher};
use std::sync::mpsc::channel;
use std::time::Duration;

impl LanguageServer {
    pub fn start(workspace_root: PathBuf) -> Result<Self> {
        let session = CompilerSession::new_for_workspace(workspace_root.clone())?;

        let (tx, rx) = channel();
        let mut watcher = watcher(tx, Duration::from_millis(500))?;
        watcher.watch(&workspace_root, RecursiveMode::Recursive)?;

        Ok(Self { session, file_watcher: watcher, watcher_rx: rx })
    }

    pub fn poll_file_events(&mut self) {
        while let Ok(event) = self.watcher_rx.try_recv() {
            match event {
                notify::DebouncedEvent::Create(path) if is_hwml_file(&path) => {
                    let text = std::fs::read_to_string(&path).unwrap_or_default();
                    self.session.add_file_to_workspace(path, text);
                }
                notify::DebouncedEvent::Remove(path) if is_hwml_file(&path) => {
                    self.session.remove_file_from_workspace(path);
                }
                notify::DebouncedEvent::Write(path) if is_hwml_file(&path) => {
                    // File modified on disk (user saved in external editor)
                    let text = std::fs::read_to_string(&path).unwrap_or_default();
                    self.session.update_file(&path, text);
                }
                _ => {}
            }
        }
    }
}
```

---

## Implementation Gotchas 🚨

Before implementing, be aware of these three critical mechanical issues:

### 1. Path Normalization is Mandatory

**Problem:** `VfsFileMap` uses `PathBuf` as HashMap keys. Different representations of the same path will cause lookup failures:
- Relative vs absolute: `lib/uart.hwml` vs `/abs/path/lib/uart.hwml`
- Case sensitivity (Windows): `C:\` vs `c:\`
- Symlinks: `/home/user/project` vs `/home/user/symlink-to-project`

**Solution:** **Always** call `normalize_path()` before any `VfsFileMap` operation. See implementation section for details.

### 2. Early Cutoff Requires `#[derive(Eq)]`

**Problem:** Without `Eq`, Salsa assumes query output changed and invalidates everything downstream.

**Solution:** All intermediate extraction types **must** derive `Eq`:
```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash)]  // ← Eq is CRITICAL!
pub struct FileImports {
    pub modules: Vec<(String, PathBuf)>,
}
```

### 3. Recursive Tree Walking Should Use Helper Functions

**Problem:** Salsa queries calling themselves can trigger cycle panics if not careful.

**Solution:** Use a regular helper function (not a `#[salsa::tracked]` query) for recursive tree walking:
```rust
// ✅ CORRECT: Helper function does recursion
fn collect_submodule_tree(db: &dyn Db, ..., tree: &mut ModuleTree) {
    let imports = file_imports(db, file);  // Query call OK
    for module in imports.modules {
        collect_submodule_tree(db, ..., tree);  // Helper recursion OK
    }
}

#[salsa::tracked]
pub fn library_module_tree(...) -> ModuleTree {
    let mut tree = ModuleTree::new();
    collect_submodule_tree(db, vfs_map, root_file, &mut tree);  // Call helper
    Ok(tree)
}
```

---

## Success Metrics

### Correctness
- [ ] `library_module_tree` is a pure `#[salsa::tracked]` query (no IO)
- [ ] `file_imports` extracts only module declarations, derives `Eq`
- [ ] All files registered in `VfsFileMap` at initialization
- [ ] File watcher updates `VfsFileMap` when files created/deleted
- [ ] Salsa invalidates module resolution when `VfsFileMap` changes
- [ ] CLI builds are hermetic (snapshot at init, immune to concurrent file changes)
- [ ] LSP shows "Module not found" error when file missing
- [ ] LSP automatically resolves module when user creates missing file

### Performance (Early Cutoff)
- [ ] **Typing in function body does NOT invalidate `library_module_tree`** ⚡
- [ ] Measured: Editing function body → only that file re-typechecked, not entire library
- [ ] LSP response time <10ms for single-file edits (measured with Salsa debug output)
- [ ] Adding a new `module` declaration DOES invalidate `library_module_tree` (correct invalidation)
- [ ] Cache hit rate >95% on incremental LSP edits to function bodies

---

## References

**rust-analyzer SourceRoot:**
- https://github.com/rust-lang/rust-analyzer/blob/master/crates/base-db/src/input.rs

**rust-analyzer ItemTree (Early Cutoff via Structural Extraction):**
- https://github.com/rust-lang/rust-analyzer/blob/master/crates/hir-def/src/item_tree.rs
- Blog post: https://rust-analyzer.github.io/blog/2020/07/20/three-architectures-for-responsive-ide.html

**Salsa Early Cutoff Documentation:**
- https://salsa-rs.github.io/salsa/common_patterns/early_cutoff.html

**File watching:**
- `notify` crate: https://docs.rs/notify/

**Related ADRs:**
- [[ADR-007-salsa-driven-compilation]] - Demand-driven queries
- [[ADR-008-vfs-abstraction]] - VFS feeds Salsa inputs
- [[ADR-006-multi-layer-build-configuration]] - Workspace manifests

---

**Status:** Approved ✅
**Next Steps:**
1. Implement `VfsFileMap` Salsa input with `Arc<HashMap<PathBuf, SourceFile>>`
2. Implement `normalize_path()` with Windows case handling
3. Implement `file_imports()` extraction query with `#[derive(Eq)]`
4. Add file discovery to `CompilerSession::new_for_workspace()`
5. Implement `library_module_tree()` query with `collect_submodule_tree()` helper
6. Integrate `notify` file watcher for LSP with path normalization
7. Test early cutoff: Edit function body → verify `library_module_tree` NOT invalidated
8. Test file creation: Create missing file → verify error disappears
9. Measure LSP response time (target: <10ms for single-file edits)


