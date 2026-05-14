//! Convert elaboration errors to rich diagnostics
//!
//! This module bridges the gap between the elaborator's internal error representation
//! (`ElabError`) and the diagnostic system's rich output format (`Diagnostic`).

use crate::error::ElabError;
use hwml_core::ty::Ty;
use hwml_core::val::GlobalEnv;
use hwml_diagnostic::{Diagnostic, DiagnosticBuilder, DiagnosticSeverity, Loctext, Position, Span};
use hwml_support::line_info::LineInfo;
use hwml_surface::parsing::ParseErrorInfo;

/// Format a type for display in error messages
fn format_type<'db, Db>(db: &'db Db, global: &GlobalEnv<'db>, ty: &Ty<'db>) -> String
where
    Db: salsa::Database,
{
    match ty {
        Ty::UniverseType => "Type".to_string(),
        Ty::SignalUniverseType => "Signal".to_string(),
        Ty::ModuleUniverseType => "Module".to_string(),
        Ty::El(code) => {
            // Quote the type code to syntax and print it
            match hwml_core::quote::type_quote(db, global, 0, code) {
                Ok(syntax) => hwml_core::syn::print::print_syntax_to_string(db, &syntax),
                Err(_) => format!("{:?}", code), // Fallback to debug format
            }
        }
        Ty::SignalEl(code) => match hwml_core::quote::type_quote(db, global, 0, code) {
            Ok(syntax) => format!(
                "Signal[{}]",
                hwml_core::syn::print::print_syntax_to_string(db, &syntax)
            ),
            Err(_) => format!("Signal[{:?}]", code),
        },
        Ty::ModuleEl(code) => match hwml_core::quote::type_quote(db, global, 0, code) {
            Ok(syntax) => format!(
                "Module[{}]",
                hwml_core::syn::print::print_syntax_to_string(db, &syntax)
            ),
            Err(_) => format!("Module[{:?}]", code),
        },
        Ty::Pi(dom, cod) => {
            // Pi types are displayed as: (x : A) → B
            // We show the domain and a placeholder for the codomain since closures are complex
            let dom_str = format_type(db, global, dom);
            format!("(x : {}) → ...", dom_str)
        }
        Ty::HArrow(source, target) => {
            // Hardware arrow types are displayed as: A → B
            let source_str = format_type(db, global, source);
            let target_str = format_type(db, global, target);
            format!("{} → {}", source_str, target_str)
        }
    }
}

/// Format a value for display in error messages (used in unification errors)
///
/// Uses type-free quotation to convert values back to syntax, then pretty-prints.
/// This handles DataConstructor and TypeConstructor values with their arguments.
fn format_value<'db, Db>(
    db: &'db Db,
    global: &GlobalEnv<'db>,
    val: &hwml_core::RcValue<'db>,
) -> String
where
    Db: salsa::Database,
{
    // Try to quote the value back to syntax using type-free quotation
    match hwml_core::quote::type_quote(db, global, 0, val) {
        Ok(syntax) => hwml_core::syn::print::print_syntax_to_string(db, &syntax),
        Err(_) => {
            // If quotation fails, fall back to simple formatting
            use hwml_core::Value;
            match val.as_ref() {
                Value::Flex(flex) => format!("?{}", flex.head.id.local_index),
                Value::Rigid(r) => format!("%{}", r.head.level.0),
                _ => format!("{:?}", val), // Last resort: debug format
            }
        }
    }
}

/// Convert an ElabError to a Diagnostic with rich formatting
///
/// This requires:
/// - Database access to resolve source file paths
/// - Global environment for type formatting
/// - Source text to compute line/column information
/// - File name for display purposes
/// - The error itself with backtrace
pub fn elab_error_to_diagnostic<'db, Db>(
    db: &'db Db,
    global: &GlobalEnv<'db>,
    error: &ElabError<'db>,
    source_text: &str,
    file_name: &str,
) -> Diagnostic
where
    Db: salsa::Database,
{
    // Compute line info for the source file
    let line_info = LineInfo::from_bytes(source_text.as_bytes());

    // Helper to convert byte offset to Position
    let byte_to_position = |offset: usize| -> Position {
        let (line_num_0, col_0) = line_info.loc(offset);
        let line_num = line_num_0 + 1; // Convert to 1-based

        // Find start of line
        let start_of_line = if line_num_0 == 0 {
            0
        } else {
            line_info.offset((line_num_0, 0))
        };

        Position::new(offset, start_of_line, line_num)
    };

    // Helper to convert Range<usize> to Span
    let range_to_span = |range: &std::ops::Range<usize>| -> Span {
        Span::new(byte_to_position(range.start), byte_to_position(range.end))
    };

    // Get the primary span from the error (or create a zero-width span at offset 0)
    // Note: Even errors without spans will use a placeholder span for the diagnostic system
    let primary_span = if let Some(source_range) = error.span() {
        range_to_span(&source_range.range)
    } else {
        // No span available, use a zero-width span at the start
        // This allows the diagnostic to be rendered even without a precise location
        Span::point(byte_to_position(0))
    };

    // Determine message and severity based on error type
    let (message, code) = match error {
        ElabError::TypeMismatch { expected, actual, .. } => {
            let expected_str = format_type(db, global, expected);
            let actual_str = format_type(db, global, actual);
            (
                format!("expected type `{}` but found type `{}`", expected_str, actual_str),
                Some("E0001"),
            )
        },
        ElabError::NotInScope { name, .. } => (
            format!("Not in scope: '{}'", name),
            Some("E0002"),
        ),
        ElabError::CannotInfer { .. } => (
            "Cannot infer type".to_string(),
            Some("E0003"),
        ),
        ElabError::UnificationFailure { lhs, rhs, .. } => {
            let lhs_str = format_value(db, global, lhs);
            let rhs_str = format_value(db, global, rhs);
            (
                format!("Type mismatch: expected '{}' but found '{}'", rhs_str, lhs_str),
                Some("E0004"),
            )
        },
        ElabError::OccursCheck { meta, .. } => (
            format!("Occurs check failed for {:?}", meta),
            Some("E0005"),
        ),
        ElabError::ScopeViolation { meta, .. } => (
            format!("Scope violation for {:?}", meta),
            Some("E0006"),
        ),
        ElabError::UnsolvedMeta { meta, .. } => (
            format!("Unsolved metavariable ?{} (this indicates the type checker could not infer enough information)", meta.0),
            Some("E0007"),
        ),
        ElabError::MetaAlreadySolved { meta, .. } => (
            format!("Meta {:?} already solved", meta),
            Some("E0008"),
        ),
        ElabError::NotImplemented { feature, .. } => (
            format!("Not implemented: {}", feature),
            Some("E0009"),
        ),
    };

    // Start building the diagnostic
    let mut builder = DiagnosticBuilder::error(primary_span, message);

    if let Some(code) = code {
        builder = builder.with_code(code);
    }

    // Add helpful suggestions for common error types
    match error {
        ElabError::CannotInfer { .. } => {
            builder = builder.with_suggestion(
                "add an explicit type annotation to help the compiler infer the type",
            );
        }
        ElabError::NotInScope { name, .. } => {
            builder = builder.with_suggestion(format!(
                "check that '{}' is defined and imported correctly",
                name
            ));
        }
        ElabError::TypeMismatch {
            expected, actual, ..
        } => {
            // Only add suggestion if types are obviously different
            if !matches!((expected.as_ref(), actual.as_ref()), (Ty::El(_), Ty::El(_))) {
                builder = builder
                    .with_suggestion("ensure the expression produces a value of the expected type");
            }
        }
        ElabError::UnsolvedMeta { meta, .. } => {
            builder = builder
                .with_explanation(format!(
                    "The type checker created an unknown placeholder (?{}) but couldn't determine what it should be. \
                     This usually happens when there's not enough type information available.",
                    meta.0
                ))
                .with_suggestion("add more type annotations to help the type checker")
                .with_suggestion("check that all function arguments and return types are specified");
        }
        _ => {
            // No specific help for other errors yet
        }
    }

    // Convert elaboration backtrace to diagnostic backtrace with narrative text
    let backtrace = error.backtrace();
    let backtrace_entries: Vec<Loctext> = backtrace
        .iter()
        .filter_map(|frame| {
            // Filter out frames with obviously wrong locations (parser bugs or default values)
            // Byte range 0..0 or 0..1 translates to line 1, column 1
            let is_bogus_location =
                frame.location.range.start == 0 && frame.location.range.end <= 1;

            if is_bogus_location {
                // Skip this frame - it has a bad location from a parser issue
                return None;
            }

            let frame_span = range_to_span(&frame.location.range);

            // Use the frame's description directly - it now contains detailed info
            // about what expression is being elaborated
            let frame_text = frame.description.clone();

            Some(Loctext::with_loc(frame_span, frame_text))
        })
        .collect();

    if !backtrace_entries.is_empty() {
        builder = builder.with_backtrace(backtrace_entries);
    }

    builder.build()
}

/// Convert a ParseErrorInfo to a Diagnostic with rich formatting
///
/// This converts surface parser errors to the same rich diagnostic format
/// used for elaboration errors.
pub fn parse_error_to_diagnostic(
    error: &ParseErrorInfo,
    source_text: &str,
    file_name: &str,
) -> Diagnostic {
    // Compute line info for the source file
    let line_info = LineInfo::from_bytes(source_text.as_bytes());

    // Helper to convert byte offset to Position
    let byte_to_position = |offset: usize| -> Position {
        let (line_num_0, col_0) = line_info.loc(offset);
        let line_num = line_num_0 + 1; // Convert to 1-based

        // Find start of line
        let start_of_line = if line_num_0 == 0 {
            0
        } else {
            line_info.offset((line_num_0, 0))
        };

        Position::new(offset, start_of_line, line_num)
    };

    // Create a zero-width span at the error location
    let error_position = byte_to_position(error.offset);
    let primary_span = Span::point(error_position);

    // Build diagnostic with error code E0100 (parse errors)
    DiagnosticBuilder::error(primary_span, error.message.clone())
        .with_code("E0100")
        .build()
}
