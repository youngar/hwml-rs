//! LSP-specific VFS implementation
//!
//! This VFS tracks editor buffers and handles unsaved changes.
//! It's designed specifically for language server use cases.

use crate::{Vfs, VfsError};
use hwml_db::db::{HwmlDatabase, SourceFile};
use lsp_types::Uri;
use salsa::Setter;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// VFS for Language Server Protocol.
///
/// Tracks open editor buffers with their latest content (including unsaved changes).
/// Falls back to disk for files not currently open in the editor.
///
/// ## Usage
///
/// ```ignore
/// let mut vfs = LspVfs::new();
/// 
/// // When editor opens a file
/// vfs.open_document(uri, path, initial_content);
///
/// // When editor modifies a file
/// vfs.update_document(uri, new_content);
///
/// // When editor closes a file
/// vfs.close_document(uri);
/// ```
pub struct LspVfs {
    /// Maps URI → (path, SourceFile)
    /// Only contains files currently open in the editor
    open_documents: HashMap<Uri, (PathBuf, SourceFile)>,
}

impl LspVfs {
    /// Create a new LSP VFS
    pub fn new() -> Self {
        Self {
            open_documents: HashMap::new(),
        }
    }

    /// Open a document in the editor
    ///
    /// This creates a new Salsa input for the file with the given content.
    /// The content represents the editor's buffer, which may differ from disk.
    pub fn open_document(
        &mut self,
        db: &HwmlDatabase,
        uri: Uri,
        path: PathBuf,
        content: String,
    ) -> SourceFile {
        let file = SourceFile::new(db, path.clone(), content);
        self.open_documents.insert(uri, (path, file));
        file
    }

    /// Update an open document's content
    ///
    /// This triggers Salsa invalidation for all queries depending on this file.
    pub fn update_document(
        &mut self,
        db: &mut HwmlDatabase,
        uri: &Uri,
        new_content: String,
    ) -> Result<(), VfsError> {
        if let Some((_, file)) = self.open_documents.get(uri) {
            file.set_text(db).to(new_content);
            Ok(())
        } else {
            Err(VfsError::FileNotFound(PathBuf::from(uri.as_str())))
        }
    }

    /// Close a document in the editor
    ///
    /// The file is removed from the open documents map.
    /// Note: The Salsa input persists in the database.
    pub fn close_document(&mut self, uri: &Uri) {
        self.open_documents.remove(uri);
    }

    /// Get a file by URI (if currently open)
    pub fn get_by_uri(&self, uri: &Uri) -> Option<SourceFile> {
        self.open_documents.get(uri).map(|(_, file)| *file)
    }

    /// Check if a document is currently open
    pub fn is_open(&self, uri: &Uri) -> bool {
        self.open_documents.contains_key(uri)
    }
}

impl Default for LspVfs {
    fn default() -> Self {
        Self::new()
    }
}

impl Vfs for LspVfs {
    fn get_or_create_file(
        &mut self,
        db: &HwmlDatabase,
        path: &Path,
    ) -> Result<SourceFile, VfsError> {
        // Try to find by path in open documents
        for (_, file) in self.open_documents.values() {
            if file.path(db) == path {
                return Ok(*file);
            }
        }

        // File not open - read from disk
        let text = std::fs::read_to_string(path).map_err(VfsError::Io)?;
        let canonical = path
            .canonicalize()
            .map_err(|_| VfsError::Canonicalization(path.to_path_buf()))?;
        
        Ok(SourceFile::new(db, canonical, text))
    }

    fn update_file(
        &mut self,
        db: &mut HwmlDatabase,
        path: &Path,
        new_text: String,
    ) -> Result<(), VfsError> {
        // Try to find by path in open documents
        for (_, file) in self.open_documents.values() {
            if file.path(db) == path {
                file.set_text(db).to(new_text);
                return Ok(());
            }
        }

        Err(VfsError::FileNotFound(path.to_path_buf()))
    }

    fn get_file(&self, path: &Path) -> Option<SourceFile> {
        self.open_documents
            .values()
            .find(|(p, _)| p == path)
            .map(|(_, file)| *file)
    }
}
