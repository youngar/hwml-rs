pub mod db;
pub mod diagnostics;
pub mod ir;
pub mod session;
pub mod workspace;

// Re-export for convenience
pub use db::{HwmlDatabase, ManifestPath, SourceFile, VfsFileMap};
pub use diagnostics::{
    file_diagnostics, workspace_diagnostics, DiagnosticCollection, DiagnosticCounts,
    FileTaggedDiagnostic,
};
pub use session::CompilerSession;
pub use workspace::{
    file_declarations, library_declarations, parse_surface_program,
    parse_surface_program_with_errors, workspace_declarations,
};
