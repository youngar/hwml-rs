//! Integration tests for hwml-diagnostic
//!
//! These tests verify that the diagnostic system works end-to-end,
//! including serialization, equality checks, and builder patterns.

use hwml_diagnostic::{
    Diagnostic, DiagnosticBuilder, DiagnosticCode, DiagnosticSeverity, Fix,
    Loctext, Position, RelatedDiagnostic, Span, Suggestion,
};
use std::path::PathBuf;

// Helper to create a simple position for testing
fn pos(offset: usize) -> Position {
    Position::new(offset, 0, 1) // Simplified for testing
}

// Helper to create a simple span for testing
fn span(start: usize, end: usize) -> Span {
    Span::new(pos(start), pos(end))
}

#[test]
fn test_diagnostic_roundtrip_serialization() {
    let original = DiagnosticBuilder::error(span(10, 20), "type mismatch")
        .with_code("E0308")
        .with_explanation("Expected Nat, found Bool")
        .with_suggestion("use an if expression")
        .build();

    // Serialize to JSON
    let json = serde_json::to_string(&original).unwrap();

    // Deserialize back
    let deserialized: Diagnostic = serde_json::from_str(&json).unwrap();

    // Should be equal
    assert_eq!(original, deserialized);
}

#[test]
fn test_complex_diagnostic_with_all_features() {
    let diagnostic = DiagnosticBuilder::error(span(42, 46), "type mismatch")
        .with_code("E0308")
        .with_explanation("The expression has type Bool but Nat was expected")
        .with_suggestion("consider using an if expression to convert to a number")
        .with_fix(
            "replace with if expression",
            Fix::Replace {
                span: span(42, 46),
                replacement: "if condition then 1 else 0".to_string(),
            },
        )
        .with_related(
            PathBuf::from("lib.hwml"),
            span(100, 120),
            "function declared here",
        )
        .with_backtrace_entry("checking function call", span(40, 50))
        .with_backtrace_entry("elaborating function body", span(35, 60))
        .build();

    // Verify all fields are set correctly
    assert_eq!(diagnostic.severity, DiagnosticSeverity::Error);
    assert_eq!(diagnostic.span.start.offset, 42);
    assert_eq!(diagnostic.span.end.offset, 46);
    assert_eq!(diagnostic.message, "type mismatch");
    assert_eq!(diagnostic.code.as_ref().unwrap().as_str(), "E0308");
    assert!(diagnostic.explanation.is_some());
    assert_eq!(diagnostic.suggestions.len(), 2);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.backtrace.len(), 2);
}

#[test]
fn test_diagnostic_equality() {
    let diag1 = DiagnosticBuilder::error(span(10, 20), "error message")
        .with_code("E0001")
        .build();

    let diag2 = DiagnosticBuilder::error(span(10, 20), "error message")
        .with_code("E0001")
        .build();

    let diag3 = DiagnosticBuilder::error(span(10, 21), "error message")
        .with_code("E0001")
        .build();

    // Same diagnostics should be equal
    assert_eq!(diag1, diag2);

    // Different span should make them not equal
    assert_ne!(diag1, diag3);
}

#[test]
fn test_severity_levels() {
    let bug = DiagnosticBuilder::bug(Span::point(pos(0)), "bug").build();
    let error = DiagnosticBuilder::error(Span::point(pos(0)), "error").build();
    let warning = DiagnosticBuilder::warning(Span::point(pos(0)), "warning").build();
    let info = DiagnosticBuilder::info(Span::point(pos(0)), "info").build();
    let hint = DiagnosticBuilder::hint(Span::point(pos(0)), "hint").build();

    assert_eq!(bug.severity, DiagnosticSeverity::Bug);
    assert_eq!(error.severity, DiagnosticSeverity::Error);
    assert_eq!(warning.severity, DiagnosticSeverity::Warning);
    assert_eq!(info.severity, DiagnosticSeverity::Info);
    assert_eq!(hint.severity, DiagnosticSeverity::Hint);

    // Verify ordering (Bug > Error > Warning > Info > Hint)
    let mut severities = vec![
        DiagnosticSeverity::Hint,
        DiagnosticSeverity::Warning,
        DiagnosticSeverity::Bug,
        DiagnosticSeverity::Error,
        DiagnosticSeverity::Info,
    ];
    severities.sort();

    // After sorting, bugs should come first, then errors, etc.
    assert_eq!(severities[0], DiagnosticSeverity::Bug);
    assert_eq!(severities[1], DiagnosticSeverity::Error);
    assert_eq!(severities[2], DiagnosticSeverity::Warning);
    assert_eq!(severities[3], DiagnosticSeverity::Info);
    assert_eq!(severities[4], DiagnosticSeverity::Hint);
}

#[test]
fn test_fix_types() {
    let replace_fix = Fix::Replace {
        span: span(10, 15),
        replacement: "new_value".to_string(),
    };

    let insert_fix = Fix::Insert {
        position: 20,
        text: "inserted text".to_string(),
    };

    let delete_fix = Fix::Delete {
        span: span(30, 40),
    };

    // All should serialize and deserialize
    let replace_json = serde_json::to_string(&replace_fix).unwrap();
    let _: Fix = serde_json::from_str(&replace_json).unwrap();

    let insert_json = serde_json::to_string(&insert_fix).unwrap();
    let _: Fix = serde_json::from_str(&insert_json).unwrap();

    let delete_json = serde_json::to_string(&delete_fix).unwrap();
    let _: Fix = serde_json::from_str(&delete_json).unwrap();
}

#[test]
fn test_builder_chaining() {
    // This test verifies that the builder pattern allows flexible chaining
    let diag = DiagnosticBuilder::warning(span(0, 10), "unused variable")
        .with_code("W0042")
        .with_suggestion("prefix with underscore")
        .with_fix(
            "add underscore prefix",
            Fix::Replace {
                span: span(0, 10),
                replacement: "_variable".to_string(),
            },
        )
        .build();

    assert_eq!(diag.severity, DiagnosticSeverity::Warning);
    assert!(diag.code.is_some());
    assert_eq!(diag.suggestions.len(), 2);
}

#[test]
fn test_loctext() {
    // Test Loctext with and without locations
    let with_loc = Loctext::with_loc(span(10, 20), "error here");
    assert!(with_loc.loc.is_some());
    assert_eq!(with_loc.text, "error here");

    let without_loc = Loctext::without_loc("general context");
    assert!(without_loc.loc.is_none());
    assert_eq!(without_loc.text, "general context");

    // Should serialize properly
    let json = serde_json::to_string(&with_loc).unwrap();
    let _: Loctext = serde_json::from_str(&json).unwrap();
}
