//! In-memory VFS implementation for hermetic testing

use crate::{Vfs, VfsError};
use hwml_db::db::{HwmlDatabase, SourceFile};
use salsa::Setter;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// In-memory VFS implementation for hermetic testing.
///
/// Unlike `OsVfs`, this never touches the filesystem. All file content
/// is stored in memory, making tests fast and reproducible.
///
/// ## Usage
///
/// ```ignore
/// let mut vfs = MemoryVfs::new();
/// vfs.add_file("/test.hwml", "module Test {}");
/// let file = vfs.get_or_create_file(&db, Path::new("/test.hwml"))?;
/// ```
pub struct MemoryVfs {
    /// Maps path → file content
    files: HashMap<PathBuf, String>,
    /// Maps path → Salsa SourceFile input
    salsa_files: HashMap<PathBuf, SourceFile>,
}

impl MemoryVfs {
    /// Create a new empty memory VFS
    pub fn new() -> Self {
        Self {
            files: HashMap::new(),
            salsa_files: HashMap::new(),
        }
    }

    /// Add a file to the memory VFS before loading
    ///
    /// This pre-populates the VFS with file content. Useful for setting up
    /// test scenarios with multiple files.
    pub fn add_file(&mut self, path: impl Into<PathBuf>, content: impl Into<String>) {
        self.files.insert(path.into(), content.into());
    }

    /// Check if a file exists in memory
    pub fn contains(&self, path: &Path) -> bool {
        self.files.contains_key(path)
    }

    /// Get the raw content of a file (not through Salsa)
    pub fn get_content(&self, path: &Path) -> Option<&str> {
        self.files.get(path).map(|s| s.as_str())
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
        db: &HwmlDatabase,
        path: &Path,
    ) -> Result<SourceFile, VfsError> {
        // Check if already loaded into Salsa
        if let Some(&file) = self.salsa_files.get(path) {
            return Ok(file);
        }

        // Get content from memory
        let text = self
            .files
            .get(path)
            .ok_or_else(|| VfsError::FileNotFound(path.to_path_buf()))?
            .clone();

        // Create Salsa input
        let file = SourceFile::new(db, path.to_path_buf(), text);
        self.salsa_files.insert(path.to_path_buf(), file);

        Ok(file)
    }

    fn update_file(
        &mut self,
        db: &mut HwmlDatabase,
        path: &Path,
        new_text: String,
    ) -> Result<(), VfsError> {
        // Update in-memory storage
        self.files.insert(path.to_path_buf(), new_text.clone());

        if let Some(&file) = self.salsa_files.get(path) {
            // Push change into Salsa (invalidates dependent queries!)
            file.set_text(db).to(new_text);
        } else {
            // File not loaded yet, create it
            let file = SourceFile::new(db, path.to_path_buf(), new_text);
            self.salsa_files.insert(path.to_path_buf(), file);
        }

        Ok(())
    }

    fn get_file(&self, path: &Path) -> Option<SourceFile> {
        self.salsa_files.get(path).copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_vfs_basic() {
        let mut vfs = MemoryVfs::new();
        vfs.add_file("/test.hwml", "test content");

        let db = HwmlDatabase::new();
        let file = vfs
            .get_or_create_file(&db, Path::new("/test.hwml"))
            .unwrap();

        assert_eq!(file.text(&db), "test content");
    }

    #[test]
    fn test_memory_vfs_file_not_found() {
        let mut vfs = MemoryVfs::new();
        let db = HwmlDatabase::new();

        let result = vfs.get_or_create_file(&db, Path::new("/missing.hwml"));
        assert!(matches!(result, Err(VfsError::FileNotFound(_))));
    }

    #[test]
    fn test_memory_vfs_caches_files() {
        let mut vfs = MemoryVfs::new();
        vfs.add_file("/test.hwml", "test");

        let db = HwmlDatabase::new();
        let file1 = vfs
            .get_or_create_file(&db, Path::new("/test.hwml"))
            .unwrap();
        let file2 = vfs
            .get_or_create_file(&db, Path::new("/test.hwml"))
            .unwrap();

        // Should be the same Salsa input ID
        assert_eq!(file1, file2);
    }

    #[test]
    fn test_memory_vfs_update() {
        let mut vfs = MemoryVfs::new();
        vfs.add_file("/test.hwml", "original");

        let mut db = HwmlDatabase::new();
        let file = vfs
            .get_or_create_file(&db, Path::new("/test.hwml"))
            .unwrap();

        assert_eq!(file.text(&db), "original");

        // Update via VFS
        vfs.update_file(&mut db, Path::new("/test.hwml"), "modified".to_string())
            .unwrap();

        // Verify Salsa input was updated
        assert_eq!(file.text(&db), "modified");
    }

    #[test]
    fn test_memory_vfs_multiple_files() {
        let mut vfs = MemoryVfs::new();
        vfs.add_file("/a.hwml", "content A");
        vfs.add_file("/b.hwml", "content B");

        let db = HwmlDatabase::new();
        let file_a = vfs.get_or_create_file(&db, Path::new("/a.hwml")).unwrap();
        let file_b = vfs.get_or_create_file(&db, Path::new("/b.hwml")).unwrap();

        assert_eq!(file_a.text(&db), "content A");
        assert_eq!(file_b.text(&db), "content B");
    }
}
