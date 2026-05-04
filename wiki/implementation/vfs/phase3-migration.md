# Phase 3: Migrate Existing Code

**Related:** [[VFS-IMPLEMENTATION-PLAN]], [[implementation/vfs/phase2-vfs-foundation]]

---

## Task 3.1: Update CLI main.rs

**File:** `crates/hwml/src/main.rs`

### Before (Surface Mode)
```rust
fn main() {
    let args = Args::parse();
    
    // Surface mode (default)
    let path = args.file.canonicalize().unwrap();
    let contents = fs::read_to_string(&path).expect("Should have been able to read the file");
    let parse_result = hwml_surface::parsing::parse(contents.as_bytes());
    
    let db = hwml_core::Database::new();
    // ...
}
```

### After (Surface Mode)
```rust
fn main() {
    let args = Args::parse();
    
    if args.core {
        run_core(args);
        return;
    }
    
    // Surface mode (default)
    let path = args.file.canonicalize().unwrap();
    
    // Create session with OS VFS
    let mut session = hwml_db::CompilerSession::new_with_os_vfs();
    
    // Load file via VFS
    let file = session.get_or_load_file(&path)
        .expect("Failed to load file");
    
    // Parse using file content
    let contents = file.text(&session.db);
    let parse_result = hwml_surface::parsing::parse(contents.as_bytes());
    
    let Some(program) = parse_result else {
        println!("Failed to parse");
        return;
    };
    
    // Use the database from session
    let db = hwml_core::Database::new();
    let mut global = hwml_core::val::GlobalEnv::new();
    let result = hwml_elab::program::elab_program(&db, &mut global, &program);
    
    // ... rest of code
}
```

### Before (Core Mode)
```rust
fn run_core(args: Args) {
    let path = args.file.canonicalize().unwrap();
    let input = fs::read_to_string(&path).expect("Should have been able to read the file");
    
    let db = hwml_core::Database::new();
    let module = match hwml_core::syn::parse_module(&db, &input) {
        // ...
    };
}
```

### After (Core Mode)
```rust
fn run_core(args: Args) {
    let path = args.file.canonicalize().unwrap();
    
    // Create session with OS VFS
    let session = hwml_db::CompilerSession::new_with_os_vfs();
    
    // Load file via VFS
    let file = session.get_or_load_file(&path)
        .expect("Failed to load file");
    
    let db = hwml_core::Database::new();
    
    // Parse using file content
    let input = file.text(&session.db);
    let module = match hwml_core::syn::parse_module(&db, input) {
        // ... rest unchanged
    };
}
```

**Remove import:**
```rust
use std::fs;  // Delete this line
```

---

## Task 3.2: Update parse_program query

**File:** `crates/hwml-db/src/db.rs`

### Before
```rust
#[salsa::tracked]
pub fn parse_program(db: &dyn salsa::Database, source_program: File) -> Program<'_> {
    // ...
    Program::new(db, vec![])
}

#[salsa::tracked]
pub fn get_line_info(db: &dyn salsa::Database, source_program: File) -> LineInfo {
    LineInfo::from_bytes(source_program.text(db).as_bytes())
}

#[salsa::tracked]
pub fn gather_diagnostics(db: &dyn salsa::Database, text_doc: File) {
    compile(db, text_doc);
}

#[salsa::tracked]
pub fn compile(db: &dyn salsa::Database, text_doc: File) {
    let _program = parse_program(db, text_doc);
}
```

### After
```rust
#[salsa::tracked]
pub fn parse_program(db: &dyn salsa::Database, source_program: SourceFile) -> Program<'_> {
    // ...
    Program::new(db, vec![])
}

#[salsa::tracked]
pub fn get_line_info(db: &dyn salsa::Database, source_program: SourceFile) -> LineInfo {
    LineInfo::from_bytes(source_program.text(db).as_bytes())
}

#[salsa::tracked]
pub fn gather_diagnostics(db: &dyn salsa::Database, text_doc: SourceFile) {
    compile(db, text_doc);
}

#[salsa::tracked]
pub fn compile(db: &dyn salsa::Database, text_doc: SourceFile) {
    let _program = parse_program(db, text_doc);
}
```

**Simple find/replace:** `File` → `SourceFile` in query signatures.

---

## Task 3.3: Update workspace loading

**File:** `crates/hwml-workspace/src/manifest.rs`

### Current Issue
```rust
pub fn load_manifest(manifest_path: &Path) -> Result<LibraryManifest, ManifestError> {
    let text = std::fs::read_to_string(manifest_path)  // ❌ Direct filesystem
        .map_err(|e| ManifestError::Io(manifest_path.to_owned(), e))?;
    // ...
}
```

### Two Options

**Option A: Keep as-is (Recommended for now)**
- Workspace manifest loading is a one-time startup operation
- Doesn't need incremental compilation
- Can stay with direct `fs::read_to_string`
- VFS is mainly for source files, not metadata

**Option B: Use VFS**
```rust
pub fn load_manifest(
    session: &hwml_db::CompilerSession,
    manifest_path: &Path,
) -> Result<LibraryManifest, ManifestError> {
    let file = session.get_or_load_file(manifest_path)
        .map_err(|e| ManifestError::Io(manifest_path.to_owned(), /* convert error */))?;
    
    let text = file.text(&session.db);
    // ... rest unchanged
}
```

**Recommendation:** Use **Option A** for Phase 3. Leave workspace loading with direct filesystem access. It's simpler and workspace manifests rarely change during compilation.

---

## Task 3.4: Update mdbook preprocessor

**File:** `crates/mdbook-hwml/src/lib.rs`

### Before
```rust
pub fn typecheck_snippet_hwmlc_accumulated(
    db: &hwml_core::Database,
    accumulated_source: &str,
    new_source: &str,
) -> Result<(), Vec<String>> {
    let combined_source = if accumulated_source.is_empty() {
        new_source.to_string()
    } else {
        format!("{}\n{}", accumulated_source, new_source)
    };
    
    let module = match hwml_core::syn::parse_module(&db, &combined_source) {
        // ...
    };
}
```

### After
```rust
pub fn typecheck_snippet_hwmlc_accumulated(
    session: &mut hwml_db::CompilerSession,  // Take session instead of db
    accumulated_source: &str,
    new_source: &str,
) -> Result<(), Vec<String>> {
    let combined_source = if accumulated_source.is_empty() {
        new_source.to_string()
    } else {
        format!("{}\n{}", accumulated_source, new_source)
    };
    
    // Create synthetic file in memory VFS
    let synthetic_path = std::path::Path::new("<snippet>");
    session.update_file(synthetic_path, combined_source)
        .map_err(|e| vec![e.to_string()])?;
    
    let file = session.get_or_load_file(synthetic_path)
        .map_err(|e| vec![e.to_string()])?;
    
    // Now parse from the VFS file
    let db = hwml_core::Database::new();
    let module = match hwml_core::syn::parse_module(&db, file.text(&session.db)) {
        Ok(m) => m,
        Err(e) => return Err(vec![format!("Parse error: {:?}", e)]),
    };
    
    // ... rest unchanged
}
```

**Update callers:**
```rust
pub fn process_chapter_content(content: &str, session_state: &mut SessionState) -> String {
    // Create session if not exists
    if session_state.session.is_none() {
        session_state.session = Some(hwml_db::CompilerSession::new_with_memory_vfs());
    }
    
    let session = session_state.session.as_mut().unwrap();
    
    // Use session in validation
    match typecheck_snippet_hwmlc_accumulated(session, accumulated, new_src) {
        // ...
    }
}
```

---

## Migration Checklist for Phase 3

- [ ] Update `hwml/src/main.rs` to use `CompilerSession`
- [ ] Remove `use std::fs` from main.rs
- [ ] Find/replace `File` → `SourceFile` in query signatures
- [ ] Update mdbook preprocessor to use `MemoryVfs`
- [ ] Leave workspace manifest loading as-is (direct fs)
- [ ] Run `cargo build` - should compile cleanly
- [ ] Run `cargo test` - most tests should pass
- [ ] Test CLI: `cargo run -- -f examples/test.hwml`

**After Phase 3:** All production code uses VFS. Tests still use tempfile (fixed in Phase 4).
