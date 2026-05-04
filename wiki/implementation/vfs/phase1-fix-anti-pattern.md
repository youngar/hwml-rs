# Phase 1: Fix Critical Anti-Pattern

**Related:** [[VFS-IMPLEMENTATION-PLAN]], [[decisions/ADR-008-vfs-abstraction]]

---

## Task 1.1: Rename File to SourceFile

**File:** `crates/hwml-db/src/db.rs`

### Before
```rust
#[salsa::input]
pub struct File {
    pub text: String,
}
```

### After
```rust
#[salsa::input]
pub struct SourceFile {
    /// Canonical absolute path to the file
    #[return_ref]
    pub path: PathBuf,
    
    /// File content as UTF-8 string
    #[return_ref]  // Critical: avoid cloning on every query
    pub text: String,
}
```

**Why `#[return_ref]`?** Without it, every call to `file.text(db)` clones the entire string. With `#[return_ref]`, Salsa returns `&String`, avoiding allocations.

---

## Task 1.2: Remove files DashMap from HwmlDatabase

**File:** `crates/hwml-db/src/db.rs`

### Before
```rust
#[salsa::db]
#[derive(Clone)]
pub struct HwmlDatabase {
    storage: salsa::Storage<Self>,
    files: DashMap<PathBuf, File>,  // ❌ Remove this!
    logs: Arc<Mutex<Option<Vec<String>>>>,
}
```

### After
```rust
#[salsa::db]
#[derive(Clone)]
pub struct HwmlDatabase {
    storage: salsa::Storage<Self>,
    // files: DashMap removed! ✅
    logs: Arc<Mutex<Option<Vec<String>>>>,
}
```

**Also remove:**
```rust
// DELETE this method entirely
pub fn input(&self, path: PathBuf) -> Result<File> {
    // ... (this logic moves to CompilerSession)
}
```

---

## Task 1.3: Create CompilerSession struct

**File:** `crates/hwml-db/src/session.rs` (NEW FILE)

```rust
use dashmap::{DashMap, Entry};
use eyre::{Context, Result};
use std::path::{Path, PathBuf};

use crate::db::{HwmlDatabase, SourceFile};

/// Compiler session that owns both the Salsa database and file cache.
/// The file cache lives OUTSIDE Salsa to follow the "VFS feeds Salsa" pattern.
pub struct CompilerSession {
    /// Salsa database for incremental queries
    pub db: HwmlDatabase,
    
    /// Cache of loaded files (path → SourceFile input)
    /// This is the "VFS" - stored outside the database!
    file_cache: DashMap<PathBuf, SourceFile>,
}

impl CompilerSession {
    pub fn new() -> Self {
        Self {
            db: HwmlDatabase::new(),
            file_cache: DashMap::new(),
        }
    }
    
    /// Get or load a file (lazy loading pattern)
    /// This is the Salsa "on-demand input" pattern:
    /// https://salsa-rs.github.io/salsa/common_patterns/on_demand_inputs.html
    pub fn get_or_load_file(&self, path: &Path) -> Result<SourceFile> {
        let canonical = path
            .canonicalize()
            .wrap_err_with(|| format!("Failed to canonicalize {}", path.display()))?;
        
        Ok(match self.file_cache.entry(canonical.clone()) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                // Read from filesystem
                let text = std::fs::read_to_string(&canonical)
                    .wrap_err_with(|| format!("Failed to read {}", canonical.display()))?;
                
                // Create Salsa input
                let file = SourceFile::new(&self.db, canonical.clone(), text);
                
                // Cache it
                *entry.insert(file)
            }
        })
    }
    
    /// Update file content (for LSP)
    /// This MUST use set_text() to trigger Salsa invalidation!
    pub fn update_file(&mut self, path: &Path, new_text: String) -> Result<()> {
        let canonical = path
            .canonicalize()
            .wrap_err_with(|| format!("Failed to canonicalize {}", path.display()))?;
        
        match self.file_cache.entry(canonical.clone()) {
            Entry::Occupied(entry) => {
                let file = *entry.get();
                // 🔥 CRITICAL: This triggers Salsa invalidation!
                file.set_text(&mut self.db).to(new_text);
                Ok(())
            }
            Entry::Vacant(entry) => {
                // File not loaded yet, create it
                let file = SourceFile::new(&mut self.db, canonical, new_text);
                entry.insert(file);
                Ok(())
            }
        }
    }
    
    /// Get already-loaded file without filesystem access
    pub fn get_file(&self, path: &Path) -> Option<SourceFile> {
        let canonical = path.canonicalize().ok()?;
        self.file_cache.get(&canonical).map(|e| *e.value())
    }
}

impl Default for CompilerSession {
    fn default() -> Self {
        Self::new()
    }
}
```

**Update `lib.rs`:**
```rust
pub mod db;
pub mod ir;
pub mod session;  // Add this

pub use session::CompilerSession;  // Re-export for convenience
```

---

## Task 1.4: Move file caching logic (DONE ABOVE)

Already completed in Task 1.3 - the `get_or_load_file()` method contains all the logic that was previously in `db.input()`.

---

## Task 1.5: Add set_text capability (DONE ABOVE)

Already completed in Task 1.3 - the `update_file()` method implements this.

---

## Testing Phase 1

**File:** `crates/hwml-db/src/session.rs` (add tests at bottom)

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;
    
    #[test]
    fn test_get_or_load_file() {
        let temp = TempDir::new().unwrap();
        let path = temp.path().join("test.hwml");
        fs::write(&path, "test content").unwrap();
        
        let session = CompilerSession::new();
        let file = session.get_or_load_file(&path).unwrap();
        
        assert_eq!(file.text(&session.db), "test content");
        assert_eq!(file.path(&session.db), &path.canonicalize().unwrap());
    }
    
    #[test]
    fn test_update_file_invalidates() {
        let temp = TempDir::new().unwrap();
        let path = temp.path().join("test.hwml");
        fs::write(&path, "original").unwrap();
        
        let mut session = CompilerSession::new();
        let file = session.get_or_load_file(&path).unwrap();
        
        assert_eq!(file.text(&session.db), "original");
        
        // Update the file content
        session.update_file(&path, "modified".to_string()).unwrap();
        
        // Verify the Salsa input was updated
        assert_eq!(file.text(&session.db), "modified");
    }
    
    #[test]
    fn test_file_cache_reuses() {
        let temp = TempDir::new().unwrap();
        let path = temp.path().join("test.hwml");
        fs::write(&path, "test").unwrap();
        
        let session = CompilerSession::new();
        let file1 = session.get_or_load_file(&path).unwrap();
        let file2 = session.get_or_load_file(&path).unwrap();
        
        // Should be the same Salsa input ID
        assert_eq!(file1, file2);
    }
}
```

---

## Migration Checklist for Phase 1

- [ ] Rename `File` → `SourceFile` globally (find/replace)
- [ ] Add `path` field to `SourceFile`
- [ ] Remove `files: DashMap` from `HwmlDatabase`
- [ ] Delete `db.input()` method
- [ ] Create `session.rs` with `CompilerSession`
- [ ] Add tests for `get_or_load_file()` and `update_file()`
- [ ] Verify all tests still pass (they will break in Phase 3, that's expected)

**Note:** After Phase 1, CLI will be broken. This is intentional - Phase 3 fixes it.
