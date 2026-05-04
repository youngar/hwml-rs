# Phase 2: VFS Foundation

**Related:** [[VFS-IMPLEMENTATION-PLAN]], [[implementation/vfs/phase1-fix-anti-pattern]]

---

## Task 2.1: Create hwml-vfs crate

**Create:** `crates/hwml-vfs/Cargo.toml`

```toml
[package]
name = "hwml-vfs"
version = "0.1.0"
edition = "2021"

[dependencies]
hwml-db = { path = "../hwml-db" }

# For LspVfs (optional, only needed for LSP)
lsp-types = { version = "0.97", optional = true }

[features]
default = []
lsp = ["dep:lsp-types"]

[dev-dependencies]
tempfile = "3.13"
```

**Update workspace:** `Cargo.toml` (root)

```toml
[workspace]
members = [
    # ... existing members
    "crates/hwml-vfs",  # Add this
]
```

---

## Task 2.2: Define Vfs trait

**Create:** `crates/hwml-vfs/src/lib.rs`

```rust
use hwml_db::{CompilerSession, SourceFile};
use std::path::Path;

pub mod memory;
pub mod os;

#[cfg(feature = "lsp")]
pub mod lsp;

/// Virtual file system abstraction.
/// 
/// The VFS lives OUTSIDE the Salsa database and feeds it SourceFile inputs.
/// Different implementations determine WHERE file content comes from:
/// - OsVfs: reads from filesystem
/// - MemoryVfs: stores in HashMap (for tests)
/// - LspVfs: tracks editor buffers (for language server)
pub trait Vfs {
    /// Get or create a SourceFile input for this path.
    /// If the file hasn't been loaded yet, reads it from the VFS source.
    fn get_or_create_file(
        &mut self,
        session: &CompilerSession,
        path: &Path,
    ) -> Result<SourceFile, VfsError>;
    
    /// Update file content (pushes change into Salsa).
    /// This triggers Salsa invalidation of all dependent queries.
    fn update_file(
        &mut self,
        session: &mut CompilerSession,
        path: &Path,
        new_text: String,
    ) -> Result<(), VfsError>;
    
    /// Get file by path (if already loaded), without triggering I/O.
    fn get_file(&self, path: &Path) -> Option<SourceFile>;
}

/// VFS error type
#[derive(Debug, thiserror::Error)]
pub enum VfsError {
    #[error("File not found: {0}")]
    FileNotFound(std::path::PathBuf),
    
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    
    #[error("Path canonicalization failed: {0}")]
    Canonicalization(std::path::PathBuf),
}

// Re-exports for convenience
pub use memory::MemoryVfs;
pub use os::OsVfs;

#[cfg(feature = "lsp")]
pub use lsp::LspVfs;
```

**Update dependencies:** `crates/hwml-vfs/Cargo.toml`

```toml
[dependencies]
hwml-db = { path = "../hwml-db" }
thiserror = "2.0"
```

---

## Task 2.3: Implement OsVfs

**Create:** `crates/hwml-vfs/src/os.rs`

```rust
use crate::{Vfs, VfsError};
use hwml_db::{CompilerSession, SourceFile};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// VFS implementation that reads from the operating system filesystem.
/// 
/// Used by CLI for normal compilation. Reads files from disk with proper
/// path canonicalization and caching.
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

impl Default for OsVfs {
    fn default() -> Self {
        Self::new()
    }
}

impl Vfs for OsVfs {
    fn get_or_create_file(
        &mut self,
        session: &CompilerSession,
        path: &Path,
    ) -> Result<SourceFile, VfsError> {
        let canonical = path.canonicalize()
            .map_err(|_| VfsError::Canonicalization(path.to_path_buf()))?;
        
        if let Some(&file) = self.files.get(&canonical) {
            return Ok(file);
        }
        
        // Read from disk upfront (hermetic snapshot)
        let text = std::fs::read_to_string(&canonical)
            .map_err(|e| VfsError::Io(e))?;
        
        // Create Salsa input
        let file = SourceFile::new(&session.db, canonical.clone(), text);
        self.files.insert(canonical, file);
        
        Ok(file)
    }
    
    fn update_file(
        &mut self,
        session: &mut CompilerSession,
        path: &Path,
        new_text: String,
    ) -> Result<(), VfsError> {
        let canonical = path.canonicalize()
            .map_err(|_| VfsError::Canonicalization(path.to_path_buf()))?;
        
        if let Some(&file) = self.files.get(&canonical) {
            // Push change into Salsa (this invalidates dependent queries!)
            file.set_text(&mut session.db).to(new_text);
        } else {
            // File not loaded yet, create it
            let file = SourceFile::new(&mut session.db, canonical.clone(), new_text);
            self.files.insert(canonical, file);
        }
        
        Ok(())
    }
    
    fn get_file(&self, path: &Path) -> Option<SourceFile> {
        let canonical = path.canonicalize().ok()?;
        self.files.get(&canonical).copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;
    
    #[test]
    fn test_os_vfs_reads_from_disk() {
        let temp = TempDir::new().unwrap();
        let path = temp.path().join("test.hwml");
        fs::write(&path, "test content").unwrap();
        
        let mut vfs = OsVfs::new();
        let session = CompilerSession::new();
        
        let file = vfs.get_or_create_file(&session, &path).unwrap();
        assert_eq!(file.text(&session.db), "test content");
    }
    
    #[test]
    fn test_os_vfs_caches_files() {
        let temp = TempDir::new().unwrap();
        let path = temp.path().join("test.hwml");
        fs::write(&path, "test").unwrap();
        
        let mut vfs = OsVfs::new();
        let session = CompilerSession::new();
        
        let file1 = vfs.get_or_create_file(&session, &path).unwrap();
        let file2 = vfs.get_or_create_file(&session, &path).unwrap();
        
        assert_eq!(file1, file2);
    }
}
```

---

## Task 2.4: Implement MemoryVfs

**Create:** `crates/hwml-vfs/src/memory.rs`

```rust
use crate::{Vfs, VfsError};
use hwml_db::{CompilerSession, SourceFile};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// VFS implementation that stores files entirely in memory.
/// 
/// Used for testing - no disk I/O, fast, hermetic.
pub struct MemoryVfs {
    files: HashMap<PathBuf, SourceFile>,
}

impl MemoryVfs {
    pub fn new() -> Self {
        Self {
            files: HashMap::new(),
        }
    }
    
    /// Convenience method: create file with initial content
    pub fn add_file(
        &mut self,
        session: &CompilerSession,
        path: impl Into<PathBuf>,
        content: impl Into<String>,
    ) -> SourceFile {
        let path = path.into();
        let content = content.into();
        let file = SourceFile::new(&session.db, path.clone(), content);
        self.files.insert(path, file);
        file
    }
}

impl Default for MemoryVfs {
    fn default() -> Self {
        Self::new()
    }
}

impl Vfs for MemoryVfs {
    fn get_or_create_file(
        &mut self,
        session: &CompilerSession,
        path: &Path,
    ) -> Result<SourceFile, VfsError> {
        if let Some(&file) = self.files.get(path) {
            return Ok(file);
        }
        
        // Create empty file if not exists
        let file = SourceFile::new(&session.db, path.to_path_buf(), String::new());
        self.files.insert(path.to_path_buf(), file);
        
        Ok(file)
    }
    
    fn update_file(
        &mut self,
        session: &mut CompilerSession,
        path: &Path,
        new_text: String,
    ) -> Result<(), VfsError> {
        if let Some(&file) = self.files.get(path) {
            file.set_text(&mut session.db).to(new_text);
        } else {
            let file = SourceFile::new(&mut session.db, path.to_path_buf(), new_text);
            self.files.insert(path.to_path_buf(), file);
        }
        
        Ok(())
    }
    
    fn get_file(&self, path: &Path) -> Option<SourceFile> {
        self.files.get(path).copied()
    }
}
```

---

## Task 2.5: Add VFS factory methods

**Update:** `crates/hwml-db/src/session.rs`

```rust
// At the top, add:
use hwml_vfs::Vfs;

// Change CompilerSession to:
pub struct CompilerSession {
    pub db: HwmlDatabase,
    vfs: Box<dyn Vfs>,  // Now uses trait object!
}

// Update methods:
impl CompilerSession {
    /// Create session with pluggable VFS
    pub fn new(vfs: Box<dyn Vfs>) -> Self {
        Self {
            db: HwmlDatabase::new(),
            vfs,
        }
    }

    /// Create session with OS filesystem VFS (for CLI)
    pub fn new_with_os_vfs() -> Self {
        Self::new(Box::new(hwml_vfs::OsVfs::new()))
    }

    /// Create session with memory VFS (for tests)
    pub fn new_with_memory_vfs() -> Self {
        Self::new(Box::new(hwml_vfs::MemoryVfs::new()))
    }

    /// Get mutable access to VFS (for adding test files)
    pub fn vfs_mut(&mut self) -> &mut dyn Vfs {
        &mut *self.vfs
    }

    // Update get_or_load_file to delegate to VFS:
    pub fn get_or_load_file(&self, path: &Path) -> Result<SourceFile> {
        self.vfs.get_or_create_file(self, path)
            .map_err(|e| eyre::eyre!("{}", e))
    }

    // Update update_file to delegate to VFS:
    pub fn update_file(&mut self, path: &Path, new_text: String) -> Result<()> {
        self.vfs.update_file(self, path, new_text)
            .map_err(|e| eyre::eyre!("{}", e))
    }
}
```

**Update dependencies:** `crates/hwml-db/Cargo.toml`

```toml
[dependencies]
salsa = "0.26"
dashmap = "6.1"
eyre = "0.6"
hwml-support = { path = "../hwml-support" }
lalrpop-util = { version = "0.22", features = ["lexer"] }
derive-new = "0.7"
hwml-vfs = { path = "../hwml-vfs" }  # Add this
```

---

## Testing Phase 2

**Create:** `crates/hwml-vfs/src/lib.rs` (add tests section)

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use hwml_db::CompilerSession;

    #[test]
    fn test_memory_vfs_basic() {
        let session = CompilerSession::new_with_memory_vfs();
        let vfs = session.vfs_mut().downcast_mut::<MemoryVfs>().unwrap();

        let file = vfs.add_file(&session, "test.hwml", "content");
        assert_eq!(file.text(&session.db), "content");
    }

    #[test]
    fn test_memory_vfs_update() {
        let mut session = CompilerSession::new_with_memory_vfs();

        // Add initial file
        {
            let vfs = session.vfs_mut().downcast_mut::<MemoryVfs>().unwrap();
            vfs.add_file(&session, "test.hwml", "original");
        }

        // Update it
        session.update_file(Path::new("test.hwml"), "modified".to_string()).unwrap();

        // Verify
        let file = session.get_or_load_file(Path::new("test.hwml")).unwrap();
        assert_eq!(file.text(&session.db), "modified");
    }
}
```

---

## Migration Checklist for Phase 2

- [ ] Create `crates/hwml-vfs/` crate with Cargo.toml
- [ ] Define `Vfs` trait in `lib.rs`
- [ ] Implement `OsVfs` in `os.rs`
- [ ] Implement `MemoryVfs` in `memory.rs`
- [ ] Update `CompilerSession` to use `Box<dyn Vfs>`
- [ ] Add factory methods (`new_with_os_vfs`, `new_with_memory_vfs`)
- [ ] Add `hwml-vfs` to workspace members
- [ ] Add dependency from `hwml-db` to `hwml-vfs`
- [ ] Run tests: `cargo test -p hwml-vfs`
- [ ] Verify trait object pattern works

**After Phase 2:** VFS abstraction is ready, but not yet used by CLI/tests. Phase 3 wires it up.
