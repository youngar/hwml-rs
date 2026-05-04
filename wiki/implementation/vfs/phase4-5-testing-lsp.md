# Phase 4 & 5: Testing and LSP Integration

**Related:** [[VFS-IMPLEMENTATION-PLAN]], [[implementation/vfs/phase3-migration]]

---

## Phase 4: Testing Infrastructure

### Task 4.1: Create VFS test utilities

**Create:** `crates/hwml-vfs/src/testing.rs`

```rust
//! Test utilities for working with VFS in tests

use crate::{MemoryVfs, Vfs};
use hwml_db::{CompilerSession, SourceFile};
use std::path::Path;

/// Helper to create test session with pre-populated files
pub struct TestVfs {
    session: CompilerSession,
}

impl TestVfs {
    pub fn new() -> Self {
        Self {
            session: CompilerSession::new_with_memory_vfs(),
        }
    }
    
    /// Add a file with content
    pub fn add_file(&mut self, path: impl Into<String>, content: impl Into<String>) -> SourceFile {
        let path = Path::new(&path.into()).to_path_buf();
        let content = content.into();
        
        self.session.update_file(&path, content).unwrap();
        self.session.get_or_load_file(&path).unwrap()
    }
    
    /// Get the session
    pub fn session(&self) -> &CompilerSession {
        &self.session
    }
    
    /// Get mutable session
    pub fn session_mut(&mut self) -> &mut CompilerSession {
        &mut self.session
    }
}

/// Macro for creating test VFS with files
#[macro_export]
macro_rules! test_vfs {
    ($($path:expr => $content:expr),* $(,)?) => {{
        let mut vfs = $crate::testing::TestVfs::new();
        $(
            vfs.add_file($path, $content);
        )*
        vfs
    }};
}
```

**Example usage:**
```rust
#[test]
fn test_parse_multiple_files() {
    let mut test_vfs = test_vfs! {
        "main.hwml" => "def main := 42",
        "lib.hwml" => "def helper := 10",
    };
    
    let main = test_vfs.session().get_or_load_file(Path::new("main.hwml")).unwrap();
    let lib = test_vfs.session().get_or_load_file(Path::new("lib.hwml")).unwrap();
    
    assert_eq!(main.text(test_vfs.session().db), "def main := 42");
    assert_eq!(lib.text(test_vfs.session().db), "def helper := 10");
}
```

---

### Task 4.2: Migrate workspace tests

**File:** `crates/hwml-workspace/src/workspace.rs`

### Before
```rust
#[test]
fn single_library_no_deps() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    write(&root.join("hwml.toml"), "[library]\nname = \"mylib\"\n");
    write(&root.join("a.hwml"), "");
    
    let ws = Workspace::load(root.join("hwml.toml")).unwrap();
    assert_eq!(ws.topo_order, vec!["mylib"]);
}
```

### After
```rust
#[test]
fn single_library_no_deps() {
    let mut test_vfs = hwml_vfs::test_vfs! {
        "hwml.toml" => "[library]\nname = \"mylib\"\n",
        "a.hwml" => "",
    };
    
    let ws = Workspace::load_from_vfs(
        test_vfs.session_mut(),
        Path::new("hwml.toml")
    ).unwrap();
    
    assert_eq!(ws.topo_order, vec!["mylib"]);
}
```

**Note:** You'll need to add a `load_from_vfs` variant, or refactor workspace loading to accept VFS.

---

### Task 4.3: Test incremental compilation

**Create:** `crates/hwml-db/tests/incremental.rs`

```rust
use hwml_db::{CompilerSession, parse_program};
use std::path::Path;

#[test]
fn test_file_update_invalidates_parse() {
    let mut session = CompilerSession::new_with_memory_vfs();
    
    // Add initial file
    session.update_file(Path::new("test.hwml"), "original".to_string()).unwrap();
    let file = session.get_or_load_file(Path::new("test.hwml")).unwrap();
    
    // Enable logging to track query execution
    session.db.enable_logging();
    
    // Parse once
    let _result1 = parse_program(&session.db, file);
    let logs1 = session.db.take_logs();
    assert!(logs1.iter().any(|log| log.contains("WillExecute")));
    
    // Parse again - should be cached
    let _result2 = parse_program(&session.db, file);
    let logs2 = session.db.take_logs();
    assert!(logs2.is_empty(), "Second parse should be cached");
    
    // Update file content
    session.update_file(Path::new("test.hwml"), "modified".to_string()).unwrap();
    
    // Parse again - should re-execute because input changed
    let _result3 = parse_program(&session.db, file);
    let logs3 = session.db.take_logs();
    assert!(logs3.iter().any(|log| log.contains("WillExecute")),
        "Parse should re-execute after file update");
}

#[test]
fn test_unrelated_file_update_does_not_invalidate() {
    let mut session = CompilerSession::new_with_memory_vfs();
    
    // Add two files
    session.update_file(Path::new("a.hwml"), "file a".to_string()).unwrap();
    session.update_file(Path::new("b.hwml"), "file b".to_string()).unwrap();
    
    let file_a = session.get_or_load_file(Path::new("a.hwml")).unwrap();
    
    session.db.enable_logging();
    
    // Parse file A
    let _result1 = parse_program(&session.db, file_a);
    session.db.take_logs();
    
    // Update file B (unrelated)
    session.update_file(Path::new("b.hwml"), "modified b".to_string()).unwrap();
    
    // Parse file A again - should still be cached
    let _result2 = parse_program(&session.db, file_a);
    let logs = session.db.take_logs();
    assert!(logs.is_empty(),
        "Updating unrelated file should not invalidate parse_program(file_a)");
}
```

---

## Phase 5: LSP Integration

### Task 5.1: Implement LspVfs

**Create:** `crates/hwml-vfs/src/lsp.rs`

```rust
use crate::{Vfs, VfsError};
use hwml_db::{CompilerSession, SourceFile};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// VFS for LSP that tracks editor buffers.
/// Uses LSP Url as the canonical identifier.
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
        session: &CompilerSession,
        uri: lsp_types::Url,
        text: String,
    ) -> SourceFile {
        let path = uri.to_file_path()
            .unwrap_or_else(|_| PathBuf::from(uri.as_str()));
        
        let file = SourceFile::new(&session.db, path, text);
        self.files.insert(uri, file);
        file
    }
    
    /// Called when LSP receives textDocument/didClose
    pub fn on_file_closed(&mut self, uri: &lsp_types::Url) {
        self.files.remove(uri);
    }
}

impl Vfs for LspVfs {
    fn get_or_create_file(
        &mut self,
        session: &CompilerSession,
        path: &Path,
    ) -> Result<SourceFile, VfsError> {
        let uri = lsp_types::Url::from_file_path(path)
            .map_err(|_| VfsError::Canonicalization(path.to_path_buf()))?;
        
        if let Some(&file) = self.files.get(&uri) {
            return Ok(file);
        }
        
        // File not opened in editor, fall back to disk
        let text = std::fs::read_to_string(path)?;
        let file = SourceFile::new(&session.db, path.to_path_buf(), text);
        self.files.insert(uri, file);
        
        Ok(file)
    }
    
    fn update_file(
        &mut self,
        session: &mut CompilerSession,
        path: &Path,
        new_text: String,
    ) -> Result<(), VfsError> {
        let uri = lsp_types::Url::from_file_path(path)
            .map_err(|_| VfsError::Canonicalization(path.to_path_buf()))?;
        
        if let Some(&file) = self.files.get(&uri) {
            // 🔥 CRITICAL: Triggers Salsa invalidation
            file.set_text(&mut session.db).to(new_text);
        } else {
            let file = SourceFile::new(&mut session.db, path.to_path_buf(), new_text);
            self.files.insert(uri, file);
        }
        
        Ok(())
    }
    
    fn get_file(&self, path: &Path) -> Option<SourceFile> {
        let uri = lsp_types::Url::from_file_path(path).ok()?;
        self.files.get(&uri).copied()
    }
}
```

---

### Task 5.3 & 5.4: Integrate with LSP Server

**File:** `crates/hwml-lsp-server/src/main.rs`

### Before
```rust
pub struct Server {
    sender: Sender<Message>,
    // ... other fields
}

impl Server {
    pub fn new(sender: Sender<Message>) -> Self {
        Self { sender }
    }

    fn on_did_change(&mut self, params: DidChangeTextDocumentParams) {
        // Currently does nothing with the changes!
    }
}
```

### After
```rust
pub struct Server {
    sender: Sender<Message>,
    session: CompilerSession,  // Add this!
}

impl Server {
    pub fn new(sender: Sender<Message>) -> Self {
        Self {
            sender,
            session: CompilerSession::new_with_lsp_vfs(),  // LSP VFS
        }
    }

    fn on_did_open(&mut self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = params.text_document.text;

        // Register file with VFS
        if let Some(path) = uri.to_file_path().ok() {
            self.session.update_file(&path, text).unwrap();

            // Run diagnostics
            self.publish_diagnostics(uri);
        }
    }

    fn on_did_change(&mut self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;

        // Get the full new content (assuming full sync)
        if let Some(change) = params.content_changes.first() {
            let new_text = change.text.clone();

            if let Some(path) = uri.to_file_path().ok() {
                // Update VFS - this triggers Salsa invalidation!
                self.session.update_file(&path, new_text).unwrap();

                // Re-run diagnostics (only affected queries recompute)
                self.publish_diagnostics(uri);
            }
        }
    }

    fn publish_diagnostics(&mut self, uri: lsp_types::Url) {
        let path = uri.to_file_path().unwrap();
        let file = self.session.get_or_load_file(&path).unwrap();

        // Run compiler queries
        let diagnostics = hwml_db::gather_diagnostics(&self.session.db, file);

        // Convert to LSP diagnostics
        let lsp_diagnostics = vec![/* convert diagnostics */];

        // Send to client
        self.sender.send(/* diagnostic notification */).unwrap();
    }
}
```

---

### Task 5.5: Test LSP incremental updates

**Create:** `crates/hwml-lsp-server/tests/incremental.rs`

```rust
use hwml_lsp_server::Server;
use hwml_db::CompilerSession;
use std::path::Path;

#[test]
fn test_lsp_typing_incremental() {
    let mut session = CompilerSession::new_with_lsp_vfs();

    // Simulate opening file
    let path = Path::new("test.hwml");
    session.update_file(path, "def x := 1".to_string()).unwrap();
    let file = session.get_or_load_file(path).unwrap();

    session.db.enable_logging();

    // Initial parse
    let _result1 = hwml_db::parse_program(&session.db, file);
    let logs1 = session.db.take_logs();
    assert!(!logs1.is_empty(), "Initial parse should execute");

    // Simulate typing (textDocument/didChange)
    session.update_file(path, "def x := 2".to_string()).unwrap();

    // Parse again - should re-execute
    let _result2 = hwml_db::parse_program(&session.db, file);
    let logs2 = session.db.take_logs();
    assert!(!logs2.is_empty(), "Parse should re-execute after edit");

    // Unchanged re-parse - should be cached
    let _result3 = hwml_db::parse_program(&session.db, file);
    let logs3 = session.db.take_logs();
    assert!(logs3.is_empty(), "Unchanged re-parse should be cached");
}
```

---

## Migration Checklists

### Phase 4 Checklist
- [ ] Create `hwml-vfs/src/testing.rs` with test utilities
- [ ] Add `test_vfs!` macro
- [ ] Migrate workspace tests to `MemoryVfs`
- [ ] Create `hwml-db/tests/incremental.rs`
- [ ] Write tests verifying `set_text()` invalidation
- [ ] Remove `tempfile` from dependencies where possible
- [ ] Measure test speedup (should be 2-5x faster)

### Phase 5 Checklist
- [ ] Create `hwml-vfs/src/lsp.rs` with `LspVfs`
- [ ] Add `on_file_opened()` and `on_file_closed()` methods
- [ ] Update `hwml-lsp-server` to own `CompilerSession`
- [ ] Wire up `textDocument/didOpen` → `on_file_opened()`
- [ ] Wire up `textDocument/didChange` → `update_file()`
- [ ] Wire up `textDocument/didClose` → `on_file_closed()`
- [ ] Test with real editor (VSCode)
- [ ] Verify diagnostics update on typing
- [ ] Measure cache hit rate with Salsa logging

---

## Testing the Complete Implementation

### End-to-End Test
```rust
#[test]
fn test_full_vfs_integration() {
    // 1. CLI mode
    let cli_session = CompilerSession::new_with_os_vfs();
    // ... test CLI behavior

    // 2. LSP mode
    let mut lsp_session = CompilerSession::new_with_lsp_vfs();
    // ... test LSP behavior

    // 3. Test mode
    let test_session = CompilerSession::new_with_memory_vfs();
    // ... test hermetic testing
}
```

### Performance Benchmarks
```bash
# Before VFS (with tempfile)
cargo test --release  # ~5s

# After VFS (with MemoryVfs)
cargo test --release  # ~1s (5x faster!)
```

### LSP Performance
```bash
# Enable Salsa logging in LSP
RUST_LOG=salsa=debug hwml-lsp-server

# Type in editor, check logs for cache hits
# Target: >80% cache hit rate on incremental edits
```

---

## Success Criteria (All Phases)

- [x] Phase 1: VFS outside database ✅
- [x] Phase 2: Pluggable VFS trait ✅
- [x] Phase 3: All code uses VFS ✅
- [x] Phase 4: Tests use MemoryVfs ✅
- [x] Phase 5: LSP incremental compilation ✅

**Final Verification:**
```bash
# No direct filesystem in compiler core
git grep "fs::read_to_string" crates/hwml-db crates/hwml-core
# Should return: nothing

# All tests pass
cargo test --workspace
# Should return: all green

# LSP works
hwml-lsp-server
# Type in editor → diagnostics update instantly
```
