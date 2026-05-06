pub mod db;
pub mod ir;
pub mod session;
pub mod workspace;

// Re-export for convenience
pub use db::{HwmlDatabase, ManifestPath, SourceFile, VfsFileMap};
pub use session::CompilerSession;
pub use workspace::{
    file_declarations, library_declarations, parse_surface_program, workspace_declarations,
};
