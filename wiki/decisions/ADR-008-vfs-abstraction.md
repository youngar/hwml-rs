# ADR-008: Virtual File System Abstraction for CLI and LSP

**Status:** Approved
**Date:** 2026-05-03
**Updated:** 2026-05-03 (Critical fix: VFS feeds Salsa inputs, doesn't hide behind RwLock)
**Deciders:** Core team
**Related:** [[ADR-007-salsa-driven-compilation]], [[research/buck2-integration-patterns]]

**⚠️ CRITICAL REVISION:** The initial version of this ADR proposed storing VFS in an `Arc<RwLock<>>` inside `HwmlDatabase`. This would have **completely broken Salsa's incremental caching**. The corrected design inverts the relationship: VFS lives outside the database and pushes changes into Salsa via `#[salsa::input]`.

---

## Context

HWML needs to read source files in three different contexts:

1. **CLI (`hwml build`):** Read files from disk (`std::fs::read_to_string`)
2. **LSP (`hwml-lsp-server`):** Read files from editor buffers (in-memory, unsaved changes)
3. **Testing:** Use synthetic in-memory files for unit tests

**The problem:** If the compiler core directly calls `std::fs::read_to_string(path)`, then:
- The LSP cannot typecheck unsaved changes (files only on disk)
- Testing requires creating temporary files on disk
- CLI and LSP require separate code paths

**The question:** Should we introduce a Virtual File System (VFS) abstraction that the compiler uses instead of direct filesystem access?

---

## Decision

**We introduce a VFS abstraction layer immediately (before implementing multi-file compilation).**

**The compiler core will NEVER directly access the filesystem.** Instead, file content is represented as Salsa inputs that the VFS populates.

**Critical architectural principle: VFS feeds Salsa, Salsa does not query VFS.**

```rust
// File content is a SALSA INPUT (not pulled from RwLock!)
#[salsa::input]
pub struct SourceFile {
    #[return_ref]
    pub path: PathBuf,

    #[return_ref] // Avoid cloning strings on every query
    pub text: String,
}
```

**The VFS lives OUTSIDE the Salsa database** and is responsible for:
1. Managing the mapping from filesystem paths/URIs to Salsa `SourceFile` inputs
2. Pushing changes into Salsa when files change (via `.set_text()`)
3. Providing the initial snapshot of files for CLI/LSP

```rust
pub struct CompilerSession {
    db: HwmlDatabase,
    vfs: Box<dyn Vfs>,
}

pub trait Vfs {
    /// Get or create a SourceFile input for this path
    fn get_or_create_file(&mut self, db: &mut HwmlDatabase, path: &Path) -> SourceFile;

    /// Update file content (pushes change into Salsa)
    fn update_file(&mut self, db: &mut HwmlDatabase, path: &Path, new_text: String);
}
```

---

## Rationale

### 1. LSP Requires Unsaved File Access

**The LSP must show errors as the user types**, before saving to disk.

**Without VFS (Broken):**
```rust
// hwml-core/src/parse.rs
pub fn parse_file(path: &Path) -> Program {
    let text = std::fs::read_to_string(path).unwrap();  // ❌ WRONG
    // ...
}
```

**Problem:** LSP receives `textDocument/didChange` events with updated text, but the file on disk is stale. Parsing from disk gives outdated errors.

**With VFS (Correct):**
```rust
// File content is a Salsa input
#[salsa::input]
pub struct SourceFile {
    #[return_ref]
    pub path: PathBuf,
    #[return_ref]
    pub text: String,
}

#[salsa::tracked]
pub fn parse_file(db: &dyn Db, file: SourceFile) -> Program {
    let text = file.text(db);  // ✅ Pure Salsa query, fully tracked
    hwml_surface::parse(text)
}
```

**LSP flow:**
```rust
struct LanguageServer {
    session: CompilerSession, // Contains db + vfs
}

fn on_did_change(&mut self, uri: Uri, new_text: String) {
    // VFS updates Salsa input
    self.session.vfs.update_file(
        &mut self.session.db,
        &uri.to_file_path().unwrap(),
        new_text
    );

    // Salsa AUTOMATICALLY invalidates parse_file() for this file!
    // No manual cache invalidation needed.
    let file = self.session.vfs.get_file(&uri.to_file_path().unwrap());
    let diagnostics = get_diagnostics(&self.session.db, file);
    send_diagnostics(uri, diagnostics);
}
```

**Why this works:** When `vfs.update_file()` calls `file.set_text(&mut db).to(new_text)`, Salsa knows the input changed and automatically invalidates all downstream queries (`parse_file`, `elaborate_file`, etc.).

### 2. Unified Testing

**Without VFS:**
```rust
#[test]
fn test_parse_error() {
    let temp_file = TempDir::new().unwrap();
    let path = temp_file.path().join("test.hwml");
    std::fs::write(&path, "invalid syntax").unwrap();

    let result = parse_file(&path);
    assert!(result.is_err());

    // Cleanup happens implicitly via TempDir drop
}
```

**Problems:**
- Slow (filesystem I/O)
- Flaky (permissions, disk space)
- Verbose (tempfile boilerplate)

**With VFS:**
```rust
#[test]
fn test_parse_error() {
    let mut session = CompilerSession::new_with_memory_vfs();

    let file = session.vfs.get_or_create_file(
        &mut session.db,
        Path::new("test.hwml")
    );

    // Set file content (pure Salsa input)
    file.set_text(&mut session.db).to("invalid syntax".to_string());

    let result = parse_file(&session.db, file);
    assert!(result.is_err());
    // No cleanup needed! No disk I/O!
}
```

### 3. Matches Industry Best Practices

**rust-analyzer** uses VFS extensively:
```rust
// rust-analyzer/crates/vfs/src/lib.rs
pub struct Vfs {
    interner: PathInterner,
    data: Vec<Option<Arc<Vec<u8>>>>,
}
```

**Sorbet** (Stripe's Ruby typechecker) uses VFS:
```cpp
// sorbet/core/FileSystem.h
class FileSystem {
  virtual string_view readFile(FileRef file) = 0;
};
```

**Language Server Protocol specification** recommends VFS:
> "The LSP assumes the client manages file system operations. The server should not directly read files from disk."

### 4. Enables Advanced Features (Future)

With VFS, we can implement:

**a) In-memory caching:**
```rust
struct CachingVfs {
    inner: Box<dyn Vfs>,
    cache: HashMap<FileId, String>,
}
```

**b) Network filesystems:**
```rust
struct RemoteVfs {
    base_url: String,
}

impl Vfs for RemoteVfs {
    fn file_text(&self, id: FileId) -> Option<String> {
        let path = self.file_path(id)?;
        reqwest::blocking::get(format!("{}/{}", self.base_url, path.display()))
            .ok()?.text().ok()
    }
}
```

**c) Overlay filesystems (for testing):**
```rust
struct OverlayVfs {
    overlay: HashMap<FileId, String>,  // Overrides
    base: Box<dyn Vfs>,                // Fallback
}
```

---

## Consequences

### Positive

1. **LSP works correctly:** Can typecheck unsaved files
2. **Faster tests:** No disk I/O in unit tests
3. **Simpler testing:** No tempfile boilerplate
4. **Unified code paths:** CLI and LSP share same compiler core
5. **Future-proof:** Enables caching, remote files, overlays

### Negative

1. **Eagerly loads all files into memory (CLI)**
   - CLI must load all files into Salsa inputs upfront
   - *Why this is actually good:* Guarantees hermetic, atomic snapshot of source code. Prevents race conditions where files change on disk mid-compilation.
   - *Memory impact:* Negligible. 1M lines of code ≈ 30-50MB of text.

2. **Complexity:** New abstraction to understand
   - *Mitigation:* VFS is a well-understood pattern (rust-analyzer, Sorbet, LSP spec).

### Critical Trap Avoided

**⚠️ The original draft of this ADR proposed storing VFS in `Arc<RwLock<>>` inside `HwmlDatabase` and querying it:**

```rust
// ❌ CATASTROPHICALLY BROKEN
#[salsa::db]
pub struct HwmlDatabase {
    storage: salsa::Storage<Self>,
    vfs: Arc<RwLock<Box<dyn Vfs>>>,  // ← TRAP!
}

#[salsa::tracked]
pub fn file_text(db: &dyn Db, file: File) -> String {
    db.vfs().file_text(file.id(db)).unwrap()  // ← BREAKS CACHING!
}
```

**Why this breaks:**
- Salsa tracks query inputs to know when to invalidate cache
- Input to `file_text(db, File(42))` is the ID `42` (which never changes)
- Actual file content is hidden behind `RwLock` side-effect
- When LSP updates file text via `vfs.update_file()`, Salsa has **no idea** the data changed
- Cache is never invalidated → LSP permanently stuck on first keystroke

**The fix:**
- File content is `#[salsa::input]` (Salsa tracks it directly)
- VFS lives outside database, pushes changes via `.set_text()`
- Salsa automatically invalidates dependent queries
- Incremental compilation works correctly

---

## Alternatives Considered

### Alternative 1: Direct Filesystem Access

**What:** Compiler directly calls `std::fs::read_to_string`

**Why rejected:**
- LSP cannot typecheck unsaved files
- Testing requires disk I/O
- CLI and LSP need separate code paths

### Alternative 2: LSP-Specific Workaround

**What:** LSP writes unsaved files to `.tmp` directory, compiler reads from there

**Why rejected:**
- Race conditions (multiple LSP instances)
- Slower (disk I/O on every keystroke)
- Doesn't solve testing problem
- Fragile (what if `.tmp` cleanup fails?)

### Alternative 3: Salsa Input for File Contents ✅ **ACCEPTED (This is the correct design!)**

**What:** Make file text a Salsa `#[salsa::input]` directly

```rust
#[salsa::input]
pub struct SourceFile {
    #[return_ref]
    pub path: PathBuf,

    #[return_ref]
    pub text: String,  // Salsa input
}
```

**Why accepted (revised decision):**

**For LSP:** This is mandatory. Salsa must track file content as an input, otherwise cache invalidation doesn't work.

**For CLI:** Eagerly loading files is actually **correct**:
1. **Hermetic builds:** Reading files upfront creates an atomic snapshot. Prevents race conditions where files change mid-compilation.
2. **Buck2 compatibility:** Remote execution requires deterministic, snapshot-based builds.
3. **Memory is cheap:** 1M lines of source code ≈ 30-50MB. Negligible on modern hardware.
4. **Matches industry practice:** rust-analyzer, Sorbet, and GHC all eagerly load files into their query systems.

**The VFS still exists**, but its role changes:
- It manages the mapping from filesystem paths to Salsa `SourceFile` inputs
- It pushes changes into Salsa (rather than Salsa pulling from VFS)
- Different VFS implementations (`OsVfs`, `LspVfs`, `MemoryVfs`) determine **where** file content comes from initially, but all push into the same Salsa input type

---

## Implementation

### Salsa Input Definition

```rust
// crates/hwml-db/src/inputs.rs

#[salsa::input]
pub struct SourceFile {
    /// Path to the file (relative to workspace root or absolute)
    #[return_ref]
    pub path: PathBuf,

    /// File content as UTF-8 string
    #[return_ref] // Critical: avoid cloning strings on every query
    pub text: String,
}
```

### VFS Trait (Feeds Salsa, Doesn't Replace It)

```rust
// crates/hwml-vfs/src/lib.rs

pub trait Vfs {
    /// Get existing SourceFile for this path, or create one
    fn get_or_create_file(
        &mut self,
        db: &mut dyn crate::Db,
        path: &Path
    ) -> SourceFile;

    /// Update file content (pushes into Salsa)
    fn update_file(
        &mut self,
        db: &mut dyn crate::Db,
        path: &Path,
        new_text: String
    );

    /// Get file by path (if already loaded)
    fn get_file(&self, path: &Path) -> Option<SourceFile>;
}
```

### OS VFS (for CLI)

```rust
pub struct OsVfs {
    /// Maps canonical path → Salsa SourceFile input
    files: HashMap<PathBuf, SourceFile>,
}

impl OsVfs {
    pub fn new() -> Self {
        Self {
            files: HashMap::new(),
        }
    }
}

impl Vfs for OsVfs {
    fn get_or_create_file(
        &mut self,
        db: &mut dyn crate::Db,
        path: &Path
    ) -> SourceFile {
        let canonical = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());

        if let Some(&file) = self.files.get(&canonical) {
            return file;
        }

        // Read from disk upfront (hermetic snapshot)
        let text = std::fs::read_to_string(&canonical)
            .unwrap_or_else(|_| String::new());

        // Create Salsa input
        let file = SourceFile::new(db, canonical.clone(), text);
        self.files.insert(canonical, file);
        file
    }

    fn update_file(
        &mut self,
        db: &mut dyn crate::Db,
        path: &Path,
        new_text: String
    ) {
        let canonical = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());

        if let Some(&file) = self.files.get(&canonical) {
            // Push change into Salsa (this invalidates dependent queries!)
            file.set_text(db).to(new_text);
        } else {
            // File not loaded yet, create it
            let file = SourceFile::new(db, canonical.clone(), new_text);
            self.files.insert(canonical, file);
        }
    }

    fn get_file(&self, path: &Path) -> Option<SourceFile> {
        let canonical = path.canonicalize().ok()?;
        self.files.get(&canonical).copied()
    }
}
```

### LSP VFS (for language server)

```rust
pub struct LspVfs {
    /// Maps URI → Salsa SourceFile input
    files: HashMap<lsp_types::Url, SourceFile>,
}

impl LspVfs {
    pub fn new() -> Self {
        Self {
            files: HashMap::new(),
        }
    }

    /// Called when LSP receives textDocument/didOpen
    pub fn on_file_opened(
        &mut self,
        db: &mut dyn crate::Db,
        uri: lsp_types::Url,
        text: String,
    ) -> SourceFile {
        let path = uri.to_file_path().unwrap_or_else(|_| PathBuf::from(uri.as_str()));

        // Create Salsa input with initial content
        let file = SourceFile::new(db, path, text);
        self.files.insert(uri, file);
        file
    }
}

impl Vfs for LspVfs {
    fn get_or_create_file(
        &mut self,
        db: &mut dyn crate::Db,
        path: &Path
    ) -> SourceFile {
        let uri = lsp_types::Url::from_file_path(path).unwrap();

        if let Some(&file) = self.files.get(&uri) {
            return file;
        }

        // If file not opened in editor yet, read from disk
        let text = std::fs::read_to_string(path).unwrap_or_default();
        let file = SourceFile::new(db, path.to_path_buf(), text);
        self.files.insert(uri, file);
        file
    }

    fn update_file(
        &mut self,
        db: &mut dyn crate::Db,
        path: &Path,
        new_text: String
    ) {
        let uri = lsp_types::Url::from_file_path(path).unwrap();

        if let Some(&file) = self.files.get(&uri) {
            // 🔥 CRITICAL: Push change into Salsa
            // This invalidates all queries dependent on this file!
            file.set_text(db).to(new_text);
        } else {
            // File not loaded, create it
            let file = SourceFile::new(db, path.to_path_buf(), new_text);
            self.files.insert(uri, file);
        }
    }

    fn get_file(&self, path: &Path) -> Option<SourceFile> {
        let uri = lsp_types::Url::from_file_path(path).ok()?;
        self.files.get(&uri).copied()
    }
}
```

### Memory VFS (for testing)

```rust
pub struct MemoryVfs {
    files: HashMap<PathBuf, SourceFile>,
}

impl MemoryVfs {
    pub fn new() -> Self {
        Self {
            files: HashMap::new(),
        }
    }
}

impl Vfs for MemoryVfs {
    fn get_or_create_file(
        &mut self,
        db: &mut dyn crate::Db,
        path: &Path
    ) -> SourceFile {
        if let Some(&file) = self.files.get(path) {
            return file;
        }

        // Create empty file
        let file = SourceFile::new(db, path.to_path_buf(), String::new());
        self.files.insert(path.to_path_buf(), file);
        file
    }

    fn update_file(
        &mut self,
        db: &mut dyn crate::Db,
        path: &Path,
        new_text: String
    ) {
        if let Some(&file) = self.files.get(path) {
            file.set_text(db).to(new_text);
        } else {
            let file = SourceFile::new(db, path.to_path_buf(), new_text);
            self.files.insert(path.to_path_buf(), file);
        }
    }

    fn get_file(&self, path: &Path) -> Option<SourceFile> {
        self.files.get(path).copied()
    }
}
```

### Compiler Session (VFS Lives Outside Database)

```rust
/// VFS lives OUTSIDE the Salsa database
pub struct CompilerSession {
    pub db: HwmlDatabase,
    pub vfs: Box<dyn Vfs>,
}

impl CompilerSession {
    pub fn new_with_os_vfs() -> Self {
        Self {
            db: HwmlDatabase::default(),
            vfs: Box::new(OsVfs::new()),
        }
    }

    pub fn new_with_lsp_vfs() -> Self {
        Self {
            db: HwmlDatabase::default(),
            vfs: Box::new(LspVfs::new()),
        }
    }

    pub fn new_with_memory_vfs() -> Self {
        Self {
            db: HwmlDatabase::default(),
            vfs: Box::new(MemoryVfs::new()),
        }
    }

    /// Load a file (creates Salsa input if needed)
    pub fn load_file(&mut self, path: &Path) -> SourceFile {
        self.vfs.get_or_create_file(&mut self.db, path)
    }

    /// Update file content (pushes into Salsa, invalidates queries)
    pub fn update_file(&mut self, path: &Path, new_text: String) {
        self.vfs.update_file(&mut self.db, path, new_text);
    }
}
```

### Queries Just Use Salsa Inputs

```rust
// No special VFS integration needed in queries!
// Just use the SourceFile input directly.

#[salsa::tracked]
pub fn parse_file(db: &dyn Db, file: SourceFile) -> Program {
    let text = file.text(db);  // Pure Salsa query
    hwml_surface::parse(text)
}

#[salsa::tracked]
pub fn elaborate_file(db: &dyn Db, file: SourceFile) -> Result<CoreTerm> {
    let program = parse_file(db, file);
    elaborate_program(db, program)
}
```

---

## Migration Path

**Phase 1 (Immediate):**
- Define `SourceFile` as `#[salsa::input]` in `hwml-db`
- Create `crates/hwml-vfs/` with `Vfs` trait
- Implement `OsVfs`, `MemoryVfs`
- Create `CompilerSession` struct (contains `db` + `vfs`)
- Update queries to take `SourceFile` instead of paths

**Phase 2 (LSP implementation):**
- Implement `LspVfs`
- LSP creates `CompilerSession::new_with_lsp_vfs()`
- On `didChange`, call `session.update_file(path, new_text)`
- Test that cache invalidation works correctly

**Phase 3 (Testing migration):**
- Convert tests to use `CompilerSession::new_with_memory_vfs()`
- Remove tempfile dependencies
- Verify no disk I/O in unit tests

**Phase 4 (Verification):**
- Test incremental compilation: change file → verify only affected queries rerun
- Test CLI hermetic builds: modify file mid-compilation → should not affect build
- Performance testing: measure cache hit rates

---

## Success Metrics

- [ ] `SourceFile` is defined as `#[salsa::input]`
- [ ] No `Arc<RwLock<Vfs>>` inside `HwmlDatabase` (VFS lives in `CompilerSession`)
- [ ] No `std::fs::read_to_string` calls in query functions
- [ ] LSP incremental compilation works (typing invalidates only affected queries)
- [ ] Unit tests use `MemoryVfs` (no disk I/O)
- [ ] CLI and LSP share same query paths
- [ ] Cache hit rate >80% on incremental LSP edits (measured with Salsa debug output)

---

## References

**rust-analyzer VFS:**
- https://github.com/rust-lang/rust-analyzer/tree/master/crates/vfs

**LSP Specification:**
- https://microsoft.github.io/language-server-protocol/specifications/specification-current/

**Related ADRs:**
- [[ADR-007-salsa-driven-compilation]] - Query-based compilation
- [[research/buck2-integration-patterns]] - Persistent worker architecture

---

**Status:** Approved
**Next Steps:**
1. Define `SourceFile` as `#[salsa::input]` in `hwml-db`
2. Create `crates/hwml-vfs/` with `Vfs` trait
3. Implement `OsVfs` and `MemoryVfs`
4. Create `CompilerSession` struct (wraps db + vfs)
5. Update queries to take `SourceFile` instead of paths
6. Write tests demonstrating incremental cache invalidation

---

## Open Question: Module Path Resolution ✅ Answered in ADR-011

**Question:** How do we map logical module paths (`open Std.Vector`) to physical file paths (`lib/std/src/vector.hwml`)?

**Answer:** See [[ADR-011-module-resolution-file-discovery]] for complete details.

**Key architecture:**

1. **FileSet Input:** All workspace files registered as Salsa input at initialization
   ```rust
   #[salsa::input]
   pub struct FileSet {
       #[return_ref]
       pub files: Arc<HashMap<PathBuf, SourceFile>>,
   }
   ```

2. **Pure Module Resolution Query:**
   ```rust
   #[salsa::tracked]
   pub fn resolve_module_path(
       db: &dyn Db,
       file_set: FileSet,  // ← Pure input, no IO!
       workspace: WorkspaceRoot,
       module_path: &[String],
   ) -> Result<SourceFile, ModuleNotFound> {
       let libs = workspace_libraries(db, workspace);
       let lib_manifest = libs.get("Std")?;

       let file_path = lib_manifest.root
           .join("src")
           .join(format!("{}.hwml", module_path[1].to_lowercase()));

       // Pure lookup (no session.load_file()!)
       file_set.files(db).get(&file_path).ok_or(NotFound)
   }
   ```

3. **File Watcher Updates FileSet:**
   - User creates `vector.hwml` → File watcher detects → Updates FileSet input
   - Salsa automatically invalidates `resolve_module_path`
   - Next compilation finds the file!

**Separation of concerns:**
- **VFS (this ADR):** Maps physical paths to file content (feeds `SourceFile` inputs)
- **Module resolution (ADR-011):** Maps logical names to physical paths (pure Salsa query over `FileSet`)
- **Both feed Salsa inputs** for proper caching and invalidation
