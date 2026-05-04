//! Operating system filesystem VFS implementation

use crate::{Vfs, VfsError};
use hwml_db::db::{HwmlDatabase, SourceFile};
use salsa::Setter;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// VFS implementation that reads from the operating system filesystem.
///
/// Used by CLI for normal compilation. Reads files from disk with proper
/// path canonicalization and caching.
///
/// ## Usage
///
/// ```ignore
/// let mut vfs = OsVfs::new();
/// let file = vfs.get_or_create_file(&db, Path::new("main.hwml"))?;
/// ```
pub struct OsVfs {
    /// Maps canonical path → Salsa SourceFile input
    files: HashMap<PathBuf, SourceFile>,
}

impl OsVfs {
    /// Create a new OS filesystem VFS
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
        db: &HwmlDatabase,
        path: &Path,
    ) -> Result<SourceFile, VfsError> {
        let canonical = path
            .canonicalize()
            .map_err(|_| VfsError::Canonicalization(path.to_path_buf()))?;

        if let Some(&file) = self.files.get(&canonical) {
            return Ok(file);
        }

        // Read from disk upfront (hermetic snapshot)
        let text = std::fs::read_to_string(&canonical).map_err(VfsError::Io)?;

        // Create Salsa input
        let file = SourceFile::new(db, canonical.clone(), text);
        self.files.insert(canonical, file);

        Ok(file)
    }

    fn update_file(
        &mut self,
        db: &mut HwmlDatabase,
        path: &Path,
        new_text: String,
    ) -> Result<(), VfsError> {
        let canonical = path
            .canonicalize()
            .map_err(|_| VfsError::Canonicalization(path.to_path_buf()))?;

        if let Some(&file) = self.files.get(&canonical) {
            // Push change into Salsa (this invalidates dependent queries!)
            file.set_text(db).to(new_text);
        } else {
            // File not loaded yet, create it
            let file = SourceFile::new(db, canonical.clone(), new_text);
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
        let db = HwmlDatabase::new();

        let file = vfs.get_or_create_file(&db, &path).unwrap();
        assert_eq!(file.text(&db), "test content");
    }

    #[test]
    fn test_os_vfs_caches_files() {
        let temp = TempDir::new().unwrap();
        let path = temp.path().join("test.hwml");
        fs::write(&path, "test").unwrap();

        let mut vfs = OsVfs::new();
        let db = HwmlDatabase::new();

        let file1 = vfs.get_or_create_file(&db, &path).unwrap();
        let file2 = vfs.get_or_create_file(&db, &path).unwrap();

        // Should be the same Salsa input ID
        assert_eq!(file1, file2);
    }

    #[test]
    fn test_os_vfs_update_file() {
        let temp = TempDir::new().unwrap();
        let path = temp.path().join("test.hwml");
        fs::write(&path, "original").unwrap();

        let mut vfs = OsVfs::new();
        let mut db = HwmlDatabase::new();

        let file = vfs.get_or_create_file(&db, &path).unwrap();
        assert_eq!(file.text(&db), "original");

        // Update via VFS
        vfs.update_file(&mut db, &path, "modified".to_string())
            .unwrap();

        // Verify Salsa input was updated
        assert_eq!(file.text(&db), "modified");
    }
}
