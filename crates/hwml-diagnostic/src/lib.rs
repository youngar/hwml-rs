//! HWML Diagnostic Framework
//!
//! This crate provides a comprehensive diagnostic system for HWML with:
//! - Rich diagnostic types (errors, warnings, hints)
//! - Multiple output formats (Terminal, LSP, JSON)
//! - Post-processing (deduplication, pattern detection, cascading analysis)
//! - Integration with Salsa for incremental computation
//!
//! # Architecture
//!
//! ```text
//! VFS → Salsa DB → file_diagnostics() → DiagnosticSystem → Output (Terminal/LSP/JSON)
//! ```
//!
//! # Example Usage
//!
//! ```ignore
//! use hwml_diagnostic::{DiagnosticBuilder, Span, DiagnosticSeverity};
//!
//! let diagnostic = DiagnosticBuilder::error(
//!     Span::new(42, 46),
//!     "type mismatch"
//! )
//! .with_code("E0308")
//! .with_explanation("Expected type Nat, but found Bool")
//! .with_suggestion("consider using an if expression")
//! .build();
//! ```

pub mod types;
pub mod builder;
pub mod ansi;
pub mod marked_source;
pub mod terminal;

// Re-export core types for convenience
pub use types::{
    Diagnostic,
    DiagnosticSeverity,
    Position,
    Span,
    Loctext,
    DiagnosticCode,
    Suggestion,
    Fix,
    RelatedDiagnostic,
};

pub use builder::DiagnosticBuilder;

// LSP integration (Week 3)
pub mod lsp;

// Feature modules (will be implemented in later weeks)
#[cfg(feature = "terminal")]
pub mod terminal;

#[cfg(feature = "json")]
pub mod json;

#[cfg(feature = "system")]
pub mod system;
