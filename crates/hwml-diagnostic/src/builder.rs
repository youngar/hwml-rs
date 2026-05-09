//! Builder pattern for constructing diagnostics ergonomically
//!
//! # Example
//!
//! ```
//! use hwml_diagnostic::{DiagnosticBuilder, Position, Span, Fix};
//!
//! // Helper to create positions for testing
//! let pos = |offset| Position::new(offset, 0, 1);
//! let span = |start, end| Span::new(pos(start), pos(end));
//!
//! let diagnostic = DiagnosticBuilder::error(
//!     span(42, 46),
//!     "type mismatch"
//! )
//! .with_code("E0308")
//! .with_explanation("Expected type Nat, but found Bool")
//! .with_suggestion("consider using an if expression")
//! .with_fix(
//!     "replace with if expression",
//!     Fix::Replace {
//!         span: span(42, 46),
//!         replacement: "if condition then value else 0".to_string(),
//!     }
//! )
//! .build();
//! ```

use crate::types::*;
use std::path::PathBuf;

/// Builder for constructing diagnostics
///
/// This provides an ergonomic API for creating diagnostics with
/// method chaining. Start with `error()`, `warning()`, etc., then
/// chain methods to add details.
pub struct DiagnosticBuilder {
    diagnostic: Diagnostic,
}

impl DiagnosticBuilder {
    /// Create a new bug diagnostic (internal compiler error)
    pub fn bug(span: Span, message: impl Into<String>) -> Self {
        Self {
            diagnostic: Diagnostic {
                severity: DiagnosticSeverity::Bug,
                span,
                message: message.into(),
                code: None,
                explanation: None,
                suggestions: Vec::new(),
                related: Vec::new(),
                backtrace: Vec::new(),
                extra_remarks: Vec::new(),
            },
        }
    }

    /// Create a new error diagnostic
    pub fn error(span: Span, message: impl Into<String>) -> Self {
        let mut builder = Self::bug(span, message);
        builder.diagnostic.severity = DiagnosticSeverity::Error;
        builder
    }

    /// Create a new warning diagnostic
    pub fn warning(span: Span, message: impl Into<String>) -> Self {
        let mut builder = Self::bug(span, message);
        builder.diagnostic.severity = DiagnosticSeverity::Warning;
        builder
    }

    /// Create a new info diagnostic
    pub fn info(span: Span, message: impl Into<String>) -> Self {
        let mut builder = Self::bug(span, message);
        builder.diagnostic.severity = DiagnosticSeverity::Info;
        builder
    }

    /// Create a new hint diagnostic
    pub fn hint(span: Span, message: impl Into<String>) -> Self {
        let mut builder = Self::bug(span, message);
        builder.diagnostic.severity = DiagnosticSeverity::Hint;
        builder
    }
    
    /// Add an error code (e.g., "E0308")
    pub fn with_code(mut self, code: impl Into<String>) -> Self {
        self.diagnostic.code = Some(DiagnosticCode::new(code));
        self
    }
    
    /// Add a detailed explanation
    pub fn with_explanation(mut self, explanation: impl Into<String>) -> Self {
        self.diagnostic.explanation = Some(explanation.into());
        self
    }
    
    /// Add a suggestion (without an automatic fix)
    pub fn with_suggestion(mut self, message: impl Into<String>) -> Self {
        self.diagnostic.suggestions.push(Suggestion {
            message: message.into(),
            fix: None,
        });
        self
    }
    
    /// Add a suggestion with an automatic fix
    pub fn with_fix(mut self, message: impl Into<String>, fix: Fix) -> Self {
        self.diagnostic.suggestions.push(Suggestion {
            message: message.into(),
            fix: Some(fix),
        });
        self
    }
    
    /// Add a related diagnostic location
    pub fn with_related(
        mut self,
        file: PathBuf,
        span: Span,
        message: impl Into<String>,
    ) -> Self {
        self.diagnostic.related.push(RelatedDiagnostic {
            file,
            span,
            message: message.into(),
        });
        self
    }
    
    /// Add a backtrace entry with location
    pub fn with_backtrace_entry(
        mut self,
        text: impl Into<String>,
        span: Span,
    ) -> Self {
        self.diagnostic.backtrace.push(Loctext::with_loc(span, text));
        self
    }

    /// Add a backtrace entry without location
    pub fn with_backtrace_text(
        mut self,
        text: impl Into<String>,
    ) -> Self {
        self.diagnostic.backtrace.push(Loctext::without_loc(text));
        self
    }

    /// Add multiple backtrace entries at once
    pub fn with_backtrace(mut self, entries: Vec<Loctext>) -> Self {
        self.diagnostic.backtrace.extend(entries);
        self
    }

    /// Add an extra remark with location
    pub fn with_remark(
        mut self,
        text: impl Into<String>,
        span: Span,
    ) -> Self {
        self.diagnostic.extra_remarks.push(Loctext::with_loc(span, text));
        self
    }

    /// Add an extra remark without location
    pub fn with_remark_text(
        mut self,
        text: impl Into<String>,
    ) -> Self {
        self.diagnostic.extra_remarks.push(Loctext::without_loc(text));
        self
    }
    
    /// Build the final diagnostic
    pub fn build(self) -> Diagnostic {
        self.diagnostic
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Helper to create a simple position for testing
    fn pos(offset: usize) -> Position {
        Position::new(offset, 0, 1) // Simplified for testing
    }

    // Helper to create a simple span for testing
    fn span(start: usize, end: usize) -> Span {
        Span::new(pos(start), pos(end))
    }

    #[test]
    fn test_bug_builder() {
        let diag = DiagnosticBuilder::bug(span(10, 20), "internal error")
            .with_code("BUG001")
            .build();

        assert_eq!(diag.severity, DiagnosticSeverity::Bug);
        assert_eq!(diag.span.start.offset, 10);
        assert_eq!(diag.span.end.offset, 20);
        assert_eq!(diag.message, "internal error");
        assert_eq!(diag.code.as_ref().unwrap().as_str(), "BUG001");
    }

    #[test]
    fn test_error_builder() {
        let diag = DiagnosticBuilder::error(span(10, 20), "test error")
            .with_code("E0001")
            .build();

        assert_eq!(diag.severity, DiagnosticSeverity::Error);
        assert_eq!(diag.span.start.offset, 10);
        assert_eq!(diag.span.end.offset, 20);
        assert_eq!(diag.message, "test error");
        assert_eq!(diag.code.as_ref().unwrap().as_str(), "E0001");
    }

    #[test]
    fn test_warning_builder() {
        let diag = DiagnosticBuilder::warning(span(0, 5), "test warning").build();
        assert_eq!(diag.severity, DiagnosticSeverity::Warning);
    }

    #[test]
    fn test_with_explanation() {
        let diag = DiagnosticBuilder::error(span(0, 1), "error")
            .with_explanation("This is a detailed explanation")
            .build();

        assert_eq!(diag.explanation.as_ref().unwrap(), "This is a detailed explanation");
    }

    #[test]
    fn test_with_suggestion() {
        let diag = DiagnosticBuilder::error(span(0, 1), "error")
            .with_suggestion("try this instead")
            .build();

        assert_eq!(diag.suggestions.len(), 1);
        assert_eq!(diag.suggestions[0].message, "try this instead");
        assert!(diag.suggestions[0].fix.is_none());
    }

    #[test]
    fn test_with_fix() {
        let diag = DiagnosticBuilder::error(span(10, 15), "error")
            .with_fix(
                "replace with correct value",
                Fix::Replace {
                    span: span(10, 15),
                    replacement: "42".to_string(),
                }
            )
            .build();

        assert_eq!(diag.suggestions.len(), 1);
        assert!(diag.suggestions[0].fix.is_some());

        if let Some(Fix::Replace { span: fix_span, replacement }) = &diag.suggestions[0].fix {
            assert_eq!(fix_span.start.offset, 10);
            assert_eq!(fix_span.end.offset, 15);
            assert_eq!(replacement, "42");
        } else {
            panic!("Expected Fix::Replace");
        }
    }

    #[test]
    fn test_with_related() {
        let diag = DiagnosticBuilder::error(span(0, 1), "error")
            .with_related(
                PathBuf::from("other.hwml"),
                span(20, 30),
                "declared here"
            )
            .build();

        assert_eq!(diag.related.len(), 1);
        assert_eq!(diag.related[0].file, PathBuf::from("other.hwml"));
        assert_eq!(diag.related[0].span.start.offset, 20);
        assert_eq!(diag.related[0].span.end.offset, 30);
        assert_eq!(diag.related[0].message, "declared here");
    }

    #[test]
    fn test_chaining() {
        let diag = DiagnosticBuilder::error(span(42, 46), "type mismatch")
            .with_code("E0308")
            .with_explanation("Expected Nat, found Bool")
            .with_suggestion("use an if expression")
            .with_related(
                PathBuf::from("main.hwml"),
                span(10, 20),
                "function declared here"
            )
            .build();

        assert_eq!(diag.severity, DiagnosticSeverity::Error);
        assert_eq!(diag.code.as_ref().unwrap().as_str(), "E0308");
        assert!(diag.explanation.is_some());
        assert_eq!(diag.suggestions.len(), 1);
        assert_eq!(diag.related.len(), 1);
    }

    #[test]
    fn test_backtrace_and_remarks() {
        let diag = DiagnosticBuilder::error(span(10, 20), "elaboration error")
            .with_backtrace_entry("checking function", span(5, 25))
            .with_backtrace_text("in module 'main'")
            .with_remark("note: this variable is shadowed", span(30, 35))
            .with_remark_text("hint: consider renaming")
            .build();

        assert_eq!(diag.backtrace.len(), 2);
        assert!(diag.backtrace[0].loc.is_some());
        assert!(diag.backtrace[1].loc.is_none());
        assert_eq!(diag.extra_remarks.len(), 2);
        assert!(diag.extra_remarks[0].loc.is_some());
        assert!(diag.extra_remarks[1].loc.is_none());
    }
}
