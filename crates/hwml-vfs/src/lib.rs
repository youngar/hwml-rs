//! Virtual File System abstraction for HWML compiler
//!
//! The VFS provides a pluggable abstraction over file sources:
//! - `OsVfs`: Reads from the operating system filesystem
//! - `MemoryVfs`: In-memory storage for testing
//! - `LspVfs`: Tracks editor buffers for the language server
//!
//! ## Architecture
//!
//! The VFS lives OUTSIDE the Salsa database and feeds it SourceFile inputs.
//! This is critical for incremental compilation to work correctly in LSP.
//!
//! See ADR-008 for the complete architectural rationale.

use hwml_db::db::{HwmlDatabase, SourceFile};
use std::path::Path;

pub mod lsp;
pub mod memory;
pub mod os;

/// Virtual file system abstraction.
///
/// The VFS lives OUTSIDE the Salsa database and feeds it SourceFile inputs.
/// Different implementations determine WHERE file content comes from:
/// - `OsVfs`: reads from filesystem
/// - `MemoryVfs`: stores in HashMap (for tests)
/// - `LspVfs`: tracks editor buffers (for language server)
///
/// ## Key Principle
///
/// **VFS feeds Salsa, Salsa does NOT query VFS.**
///
/// When file content changes, the VFS calls `file.set_text(&mut db).to(new_text)`,
/// which triggers Salsa's incremental invalidation automatically.
pub trait Vfs {
    /// Get or create a SourceFile input for this path.
    ///
    /// If the file hasn't been loaded yet, reads it from the VFS source
    /// (filesystem, memory, etc.) and creates a new Salsa input.
    fn get_or_create_file(
        &mut self,
        db: &HwmlDatabase,
        path: &Path,
    ) -> Result<SourceFile, VfsError>;

    /// Update file content (pushes change into Salsa).
    ///
    /// This triggers Salsa invalidation of all dependent queries.
    /// This is THE critical method for LSP incremental compilation.
    fn update_file(
        &mut self,
        db: &mut HwmlDatabase,
        path: &Path,
        new_text: String,
    ) -> Result<(), VfsError>;

    /// Get file by path (if already loaded), without triggering I/O.
    ///
    /// Returns None if the file hasn't been loaded yet.
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
pub use lsp::LspVfs;
pub use memory::MemoryVfs;
pub use os::OsVfs;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vfs_error_display() {
        let err = VfsError::FileNotFound(std::path::PathBuf::from("test.hwml"));
        assert!(err.to_string().contains("test.hwml"));

        let err = VfsError::Canonicalization(std::path::PathBuf::from("bad/path"));
        assert!(err.to_string().contains("bad/path"));
    }
}
