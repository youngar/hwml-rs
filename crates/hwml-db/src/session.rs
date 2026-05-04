use dashmap::{DashMap, Entry};
use eyre::{Context, Result};
use salsa::Setter;
use std::path::{Path, PathBuf};

use crate::db::{HwmlDatabase, SourceFile};

/// Compiler session that owns both the Salsa database and file cache.
///
/// The file cache lives OUTSIDE Salsa to follow the "VFS feeds Salsa" pattern.
/// This is critical for LSP incremental compilation to work correctly.
///
/// See ADR-008 for the architectural rationale.
pub struct CompilerSession {
    /// Salsa database for incremental queries
    pub db: HwmlDatabase,

    /// Cache of loaded files (path → SourceFile input)
    /// This is the "VFS" - stored outside the database!
    file_cache: DashMap<PathBuf, SourceFile>,
}

impl CompilerSession {
    /// Create a new compiler session with an empty file cache
    pub fn new() -> Self {
        Self {
            db: HwmlDatabase::new(),
            file_cache: DashMap::new(),
        }
    }

    /// Get or load a file (lazy loading pattern)
    ///
    /// This is the Salsa "on-demand input" pattern:
    /// https://salsa-rs.github.io/salsa/common_patterns/on_demand_inputs.html
    ///
    /// If the file is already cached, returns it immediately.
    /// Otherwise, reads from filesystem and creates a new Salsa input.
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
    ///
    /// This MUST use set_text() to trigger Salsa invalidation!
    /// When set_text() is called, Salsa automatically invalidates all
    /// queries that depend on this file's content.
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
    ///
    /// Returns None if the file hasn't been loaded yet.
    /// Use get_or_load_file() if you want to load it automatically.
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
