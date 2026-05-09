use dashmap::{DashMap, Entry};
use eyre::{Context, Result};
use salsa::Setter;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::db::{HwmlDatabase, SourceFile, VfsFileMap};

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

    /// Optional VfsFileMap for module resolution
    /// This tracks all known files in the workspace and is used by module resolution queries
    vfs_file_map: Option<VfsFileMap>,
}

impl CompilerSession {
    /// Create a new compiler session with an empty file cache
    pub fn new() -> Self {
        Self {
            db: HwmlDatabase::new(),
            file_cache: DashMap::new(),
            vfs_file_map: None,
        }
    }

    /// Normalize a path to canonical absolute form
    ///
    /// This is CRITICAL for VfsFileMap operations to work correctly.
    /// All paths must be normalized before using as HashMap keys.
    ///
    /// See ADR-011 "Implementation Gotchas" section for details.
    pub fn normalize_path(&self, path: &Path) -> Result<PathBuf> {
        // Try to canonicalize (resolves symlinks, makes absolute)
        match path.canonicalize() {
            Ok(canonical) => {
                // On Windows, ensure drive letter is uppercase
                #[cfg(windows)]
                let canonical = normalize_windows_path(canonical);
                Ok(canonical)
            }
            Err(_) => {
                // File might not exist yet (e.g., being created in editor)
                // Manually make absolute relative to current directory
                let abs = if path.is_absolute() {
                    path.to_path_buf()
                } else {
                    std::env::current_dir()?.join(path)
                };

                #[cfg(windows)]
                let abs = normalize_windows_path(abs);

                Ok(abs)
            }
        }
    }

    /// Create a session initialized with all .hwml files in a workspace
    ///
    /// This eagerly scans the workspace and creates a VfsFileMap input
    /// that module resolution queries can use for pure lookups.
    pub fn new_for_workspace(workspace_root: PathBuf) -> Result<Self> {
        let mut session = Self::new();

        // Discover all .hwml files in the workspace
        let discovered_files = discover_hwml_files(&workspace_root)?;

        // Create Salsa SourceFile inputs for each discovered file
        let mut file_map = HashMap::new();
        for path in discovered_files {
            let canonical = session.normalize_path(&path)?;
            let text = std::fs::read_to_string(&canonical)
                .wrap_err_with(|| format!("Failed to read {}", canonical.display()))?;

            let source_file = SourceFile::new(&mut session.db, canonical.clone(), text, "interactive".to_string());

            // Add to file cache
            session.file_cache.insert(canonical.clone(), source_file);

            // Add to file map with PathBuf as key
            file_map.insert(canonical, source_file);
        }

        // Create VfsFileMap Salsa input
        let vfs_file_map = VfsFileMap::new(&mut session.db, Arc::new(file_map));
        session.vfs_file_map = Some(vfs_file_map);

        Ok(session)
    }

    /// Get the VfsFileMap for this session (if initialized)
    pub fn vfs_file_map(&self) -> Option<VfsFileMap> {
        self.vfs_file_map
    }

    /// Add a file to the workspace VfsFileMap
    ///
    /// This is called by the file watcher when a new .hwml file is created.
    /// Updating the VfsFileMap triggers Salsa invalidation of module resolution queries.
    pub fn add_file_to_workspace(&mut self, path: PathBuf, text: String) -> Result<()> {
        let canonical = self.normalize_path(&path)?;

        // Create Salsa SourceFile input
        let source_file = SourceFile::new(&mut self.db, canonical.clone(), text, "interactive".to_string());

        // Add to file cache
        self.file_cache.insert(canonical.clone(), source_file);

        // Update VfsFileMap if it exists
        if let Some(vfs_map) = self.vfs_file_map {
            // Clone the Arc (cheap - just increments refcount)
            let mut files = (**vfs_map.files(&self.db)).clone();
            files.insert(canonical, source_file);

            // Update Salsa input (THIS TRIGGERS INVALIDATION!)
            vfs_map.set_files(&mut self.db).to(Arc::new(files));
        }

        Ok(())
    }

    /// Remove a file from the workspace VfsFileMap
    ///
    /// This is called by the file watcher when a .hwml file is deleted.
    /// Updating the VfsFileMap triggers Salsa invalidation of module resolution queries.
    pub fn remove_file_from_workspace(&mut self, path: &Path) -> Result<()> {
        let canonical = self.normalize_path(path)?;

        // Remove from file cache
        self.file_cache.remove(&canonical);

        // Update VfsFileMap if it exists
        if let Some(vfs_map) = self.vfs_file_map {
            let mut files = (**vfs_map.files(&self.db)).clone();
            files.remove(&canonical);

            // Update Salsa input (THIS TRIGGERS INVALIDATION!)
            vfs_map.set_files(&mut self.db).to(Arc::new(files));
        }

        Ok(())
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
                let file = SourceFile::new(&self.db, canonical.clone(), text, "interactive".to_string());

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
                let file = SourceFile::new(&mut self.db, canonical, new_text, "interactive".to_string());
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

/// Discover all .hwml files in a directory tree
///
/// Walks the directory recursively and returns canonical paths to all .hwml files.
fn discover_hwml_files(root: &Path) -> Result<Vec<PathBuf>> {
    let mut files = Vec::new();

    let root_canonical = root.canonicalize()?;

    for entry in walkdir::WalkDir::new(root)
        .follow_links(false) // Don't follow symlinks to avoid cycles
        .into_iter()
        .filter_entry(|e| {
            // Don't filter the root directory itself
            if e.path() == root || e.path() == root_canonical {
                return true;
            }

            // Skip hidden directories and common ignore patterns
            let name = e.file_name().to_string_lossy();
            !name.starts_with('.') && name != "target" && name != "node_modules"
        })
    {
        let entry = entry?;
        let path = entry.path();

        // Check if it's a .hwml file
        if path.is_file() {
            if let Some(ext) = path.extension() {
                if ext == "hwml" {
                    // Canonicalize the path
                    let canonical = path
                        .canonicalize()
                        .wrap_err_with(|| format!("Failed to canonicalize {}", path.display()))?;
                    files.push(canonical);
                }
            }
        }
    }

    Ok(files)
}

/// Normalize Windows paths to have uppercase drive letters
/// This ensures consistent HashMap keys across different Windows path representations
#[cfg(windows)]
fn normalize_windows_path(path: PathBuf) -> PathBuf {
    use std::path::Component;

    let mut components = path.components();
    if let Some(Component::Prefix(prefix)) = components.next() {
        let prefix_str = prefix.as_os_str().to_string_lossy();

        // Check if it's a drive letter (e.g., "C:" or "c:")
        if prefix_str.len() >= 2 && prefix_str.chars().nth(1) == Some(':') {
            let drive = prefix_str.chars().next().unwrap().to_ascii_uppercase();
            let rest: PathBuf = components.collect();
            return PathBuf::from(format!("{}:{}", drive, rest.display()));
        }
    }

    path
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

    #[test]
    fn test_workspace_initialization() {
        // Create a temp workspace with multiple .hwml files
        let temp = TempDir::new().unwrap();

        // Create some .hwml files in root
        fs::write(temp.path().join("lib.hwml"), "// lib").unwrap();
        fs::write(temp.path().join("mod1.hwml"), "// mod1").unwrap();

        // Create a subdirectory with another file
        let subdir = temp.path().join("subdir");
        fs::create_dir(&subdir).unwrap();
        fs::write(subdir.join("mod2.hwml"), "// mod2").unwrap();

        // Initialize workspace
        let session = CompilerSession::new_for_workspace(temp.path().to_path_buf()).unwrap();

        // Should have discovered all 3 files
        let vfs_map = session
            .vfs_file_map()
            .expect("VfsFileMap should be initialized");
        let files = vfs_map.files(&session.db);

        assert_eq!(files.len(), 3, "Should discover 3 .hwml files");

        // Verify each file was loaded correctly
        for (path, source_file) in files.iter() {
            // Check extension properly
            assert_eq!(
                path.extension(),
                Some(std::ffi::OsStr::new("hwml")),
                "Path should have .hwml extension: {}",
                path.display()
            );
            assert!(source_file.text(&session.db).starts_with("//"));
        }
    }

    #[test]
    fn test_add_file_to_workspace() {
        let temp = TempDir::new().unwrap();
        let src = temp.path().join("src");
        fs::create_dir(&src).unwrap();
        fs::write(src.join("lib.hwml"), "// lib").unwrap();

        let mut session = CompilerSession::new_for_workspace(temp.path().to_path_buf()).unwrap();

        // Initially 1 file
        assert_eq!(session.vfs_file_map().unwrap().files(&session.db).len(), 1);

        // Add a new file
        let new_file = src.join("new.hwml");
        session
            .add_file_to_workspace(new_file.clone(), "// new".to_string())
            .unwrap();

        // Should now have 2 files
        assert_eq!(session.vfs_file_map().unwrap().files(&session.db).len(), 2);

        // Verify the new file is in the map
        let canonical = session.normalize_path(&new_file).unwrap();
        assert!(session
            .vfs_file_map()
            .unwrap()
            .files(&session.db)
            .contains_key(&canonical));
    }

    #[test]
    fn test_remove_file_from_workspace() {
        let temp = TempDir::new().unwrap();
        let src = temp.path().join("src");
        fs::create_dir(&src).unwrap();

        let file1 = src.join("file1.hwml");
        let file2 = src.join("file2.hwml");
        fs::write(&file1, "// file1").unwrap();
        fs::write(&file2, "// file2").unwrap();

        let mut session = CompilerSession::new_for_workspace(temp.path().to_path_buf()).unwrap();

        // Initially 2 files
        assert_eq!(session.vfs_file_map().unwrap().files(&session.db).len(), 2);

        // Remove one file
        session.remove_file_from_workspace(&file1).unwrap();

        // Should now have 1 file
        assert_eq!(session.vfs_file_map().unwrap().files(&session.db).len(), 1);

        // Verify file1 is gone but file2 remains
        let canonical1 = session.normalize_path(&file1).unwrap();
        let canonical2 = session.normalize_path(&file2).unwrap();

        let files = session.vfs_file_map().unwrap().files(&session.db);
        assert!(!files.contains_key(&canonical1));
        assert!(files.contains_key(&canonical2));
    }
}
