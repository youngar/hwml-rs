//! Core diagnostic types for HWML
//!
//! This module defines the fundamental types for representing diagnostics:
//! - Errors, warnings, hints
//! - Source locations (spans)
//! - Auto-fix suggestions
//! - Related diagnostic locations
//! - Elaboration backtraces

use serde::{Deserialize, Serialize};
use std::path::PathBuf;

/// A single diagnostic (error, warning, hint, etc.)
///
/// Diagnostics are rich data structures that include:
/// - Severity level (Bug/Error/Warning/Info/Hint)
/// - Source location (Position-based span)
/// - Primary message
/// - Optional error code (e.g., "E0308")
/// - Optional detailed explanation (for `--explain`)
/// - Auto-fix suggestions
/// - Related diagnostic locations (for multi-file errors)
/// - Elaboration backtrace (showing execution context)
/// - Extra remarks (additional source notes)
///
/// Based on Asai's diagnostic structure with separated backtrace and remarks.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Diagnostic {
    /// Severity level
    pub severity: DiagnosticSeverity,

    /// Byte span in source file
    pub span: Span,

    /// Primary message
    pub message: String,

    /// Error code (e.g., "E0001", "W0042", "BUG001")
    pub code: Option<DiagnosticCode>,

    /// Detailed explanation (for `--explain`)
    pub explanation: Option<String>,

    /// Suggested fixes
    pub suggestions: Vec<Suggestion>,

    /// Related diagnostic locations (for multi-file errors)
    pub related: Vec<RelatedDiagnostic>,

    /// Elaboration backtrace (execution context from trace guards)
    ///
    /// Shows the path through the elaborator that led to this diagnostic.
    /// Example: ["checking function 'main'", "checking let binding", "unifying types"]
    pub backtrace: Vec<Loctext>,

    /// Extra remarks (additional source notes)
    ///
    /// Used for showing related source locations with explanations.
    /// Example: "Note: 'x' was defined here"
    pub extra_remarks: Vec<Loctext>,
}

/// Severity level for diagnostics
///
/// Ordered from most to least severe (Bug > Error > Warning > Info > Hint).
/// The `Ord` implementation allows sorting diagnostics by severity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DiagnosticSeverity {
    /// Internal compiler bug - the compiler has a bug, not the user's code.
    /// Users should report these as GitHub issues.
    ///
    /// Example: "elaborator panic: unexpected None in solve_constraint"
    Bug,

    /// User error - the code is incorrect and cannot be compiled.
    ///
    /// Example: "type mismatch: expected Nat, found Bool"
    Error,

    /// Warning - the code is suspicious but might be intentional.
    ///
    /// Example: "unused variable 'x'"
    Warning,

    /// Informational message - FYI, not a problem.
    ///
    /// Example: "inferred type for 'x' is Nat"
    Info,

    /// Hint - code smell or style suggestion.
    ///
    /// Example: "this pattern match could be simplified"
    Hint,
}

// Custom Ord implementation to ensure Bug > Error > Warning > Info > Hint
impl PartialOrd for DiagnosticSeverity {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for DiagnosticSeverity {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use DiagnosticSeverity::*;
        let priority = |s: &DiagnosticSeverity| match s {
            Bug => 0,
            Error => 1,
            Warning => 2,
            Info => 3,
            Hint => 4,
        };
        priority(self).cmp(&priority(other))
    }
}

/// A position in source code with cached line information
///
/// This type stores both the byte offset (for precise source slicing) and
/// cached line information (for fast rendering without repeated line scans).
///
/// Based on Asai's Range.position type (see ADR-017).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Position {
    /// Byte offset from start of file (0-indexed)
    pub offset: usize,

    /// Byte offset of the start of this line (0-indexed)
    pub start_of_line: usize,

    /// Line number (1-indexed, matching LSP and user expectations)
    pub line_num: usize,
}

impl Position {
    /// Create a new position with all fields
    pub fn new(offset: usize, start_of_line: usize, line_num: usize) -> Self {
        Self { offset, start_of_line, line_num }
    }

    /// Column number (0-indexed) within the line
    ///
    /// This is O(1) thanks to caching start_of_line.
    pub fn column(&self) -> usize {
        self.offset.saturating_sub(self.start_of_line)
    }
}

/// Source location as a span between two positions
///
/// Byte offsets are used because:
/// 1. They're stable across edits (unlike line:column)
/// 2. They're fast to compute during parsing
/// 3. Line information is cached for fast rendering (see ADR-017)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Span {
    /// Start position (inclusive)
    pub start: Position,

    /// End position (exclusive)
    pub end: Position,
}

impl Span {
    /// Create a new span from two positions
    pub fn new(start: Position, end: Position) -> Self {
        Self { start, end }
    }

    /// Create a zero-width span at a position
    pub fn point(pos: Position) -> Self {
        Self { start: pos, end: pos }
    }

    /// Check if this span contains a byte offset
    pub fn contains(&self, offset: usize) -> bool {
        self.start.offset <= offset && offset < self.end.offset
    }

    /// Get the length of this span in bytes
    pub fn len(&self) -> usize {
        self.end.offset.saturating_sub(self.start.offset)
    }

    /// Check if this is a zero-width span
    pub fn is_empty(&self) -> bool {
        self.start.offset == self.end.offset
    }

    /// Get the byte range for source text extraction
    pub fn byte_range(&self) -> std::ops::Range<usize> {
        self.start.offset..self.end.offset
    }
}

/// Text with an optional source location
///
/// This type is used for diagnostic explanations, remarks, and backtrace entries
/// that may or may not have an associated source location.
///
/// Based on Asai's Loctext type.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Loctext {
    /// Optional source location
    pub loc: Option<Span>,

    /// Text content
    pub text: String,
}

impl Loctext {
    /// Create located text with a span
    pub fn with_loc(loc: Span, text: impl Into<String>) -> Self {
        Self {
            loc: Some(loc),
            text: text.into(),
        }
    }

    /// Create text without a location
    pub fn without_loc(text: impl Into<String>) -> Self {
        Self {
            loc: None,
            text: text.into(),
        }
    }
}

/// Diagnostic error code (e.g., "E0308", "W0042")
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiagnosticCode(pub String);

impl DiagnosticCode {
    /// Create a new diagnostic code
    pub fn new(code: impl Into<String>) -> Self {
        Self(code.into())
    }
    
    /// Get the code as a string
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for DiagnosticCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A suggestion for fixing a diagnostic
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Suggestion {
    /// Description of what to change
    pub message: String,
    
    /// Optional automated fix
    pub fix: Option<Fix>,
}

/// An automated code fix
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Fix {
    /// Replace a range with new text
    Replace {
        span: Span,
        replacement: String,
    },

    /// Insert text at a position
    Insert {
        position: usize,
        text: String,
    },

    /// Delete a range
    Delete {
        span: Span,
    },
}

/// A related diagnostic location
///
/// Used to show connections between diagnostics across files.
/// For example, a type mismatch error might have a related location
/// pointing to where the function was declared.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RelatedDiagnostic {
    /// File path where related location is
    /// Using PathBuf instead of SourceFile to avoid Salsa dependency in types
    pub file: PathBuf,

    /// Span in that file
    pub span: Span,

    /// Message explaining the relationship
    pub message: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    // Helper to create a simple position for testing
    fn pos(offset: usize) -> Position {
        Position::new(offset, 0, 1) // Simplified for testing
    }

    #[test]
    fn test_position_column() {
        let p = Position::new(42, 30, 3);
        assert_eq!(p.column(), 12); // 42 - 30 = 12
    }

    #[test]
    fn test_span_contains() {
        let span = Span::new(pos(10), pos(20));
        assert!(span.contains(10));
        assert!(span.contains(15));
        assert!(span.contains(19));
        assert!(!span.contains(20)); // end is exclusive
        assert!(!span.contains(9));
    }

    #[test]
    fn test_span_len() {
        assert_eq!(Span::new(pos(10), pos(20)).len(), 10);
        assert_eq!(Span::new(pos(0), pos(5)).len(), 5);
        assert_eq!(Span::point(pos(42)).len(), 0);
    }

    #[test]
    fn test_span_is_empty() {
        assert!(Span::point(pos(42)).is_empty());
        assert!(!Span::new(pos(10), pos(20)).is_empty());
    }

    #[test]
    fn test_loctext() {
        let with_loc = Loctext::with_loc(Span::new(pos(10), pos(20)), "error here");
        assert!(with_loc.loc.is_some());
        assert_eq!(with_loc.text, "error here");

        let without_loc = Loctext::without_loc("general note");
        assert!(without_loc.loc.is_none());
        assert_eq!(without_loc.text, "general note");
    }

    #[test]
    fn test_diagnostic_code_display() {
        let code = DiagnosticCode::new("E0308");
        assert_eq!(code.to_string(), "E0308");
        assert_eq!(code.as_str(), "E0308");
    }

    #[test]
    fn test_diagnostic_severity_ord() {
        // Test that severities sort correctly (Bug > Error > Warning > Info > Hint)
        let mut severities = vec![
            DiagnosticSeverity::Hint,
            DiagnosticSeverity::Info,
            DiagnosticSeverity::Warning,
            DiagnosticSeverity::Error,
            DiagnosticSeverity::Bug,
        ];
        severities.sort();

        // After sorting, Bug should come first, then Error, etc.
        assert_eq!(severities, vec![
            DiagnosticSeverity::Bug,
            DiagnosticSeverity::Error,
            DiagnosticSeverity::Warning,
            DiagnosticSeverity::Info,
            DiagnosticSeverity::Hint,
        ]);
    }
}
