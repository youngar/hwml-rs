//! Terminal rendering for diagnostics with ANSI colors
//!
//! This module provides functions to render diagnostics to the terminal
//! with nice colors and formatting.

use crate::ansi::{color, style};
use crate::types::{Diagnostic, DiagnosticSeverity};

/// Render a diagnostic to a string with ANSI colors
///
/// # Arguments
/// * `diagnostic` - The diagnostic to render
/// * `file_name` - Optional file name to display in the location (if None, only line:column shown)
pub fn render_diagnostic(diagnostic: &Diagnostic, file_name: Option<&str>) -> String {
    let mut output = String::new();

    // Render severity and message
    let severity_str = match diagnostic.severity {
        DiagnosticSeverity::Bug => format!("{}{}BUG{}", color::BUG, style::BOLD, style::RESET),
        DiagnosticSeverity::Error => format!("{}{}error{}", color::RED, style::BOLD, style::RESET),
        DiagnosticSeverity::Warning => format!("{}{}warning{}", color::YELLOW, style::BOLD, style::RESET),
        DiagnosticSeverity::Info => format!("{}{}info{}", color::GREEN, style::BOLD, style::RESET),
        DiagnosticSeverity::Hint => format!("{}{}hint{}", color::BLUE, style::BOLD, style::RESET),
    };

    // Add error code if present
    let code_str = if let Some(code) = &diagnostic.code {
        format!("[{}]", code)
    } else {
        String::new()
    };

    output.push_str(&format!("{}{}: {}\n", severity_str, code_str, diagnostic.message));

    // Render primary location
    let location_str = if let Some(fname) = file_name {
        format!("{}:{}:{}", fname, diagnostic.span.start.line_num, diagnostic.span.start.column() + 1)
    } else {
        format!("line {}, column {}", diagnostic.span.start.line_num, diagnostic.span.start.column() + 1)
    };
    output.push_str(&format!("  {}-->{}  {}\n",
        style::DIM,
        style::RESET,
        location_str,
    ));
    
    // Render backtrace if present - narrative style
    if !diagnostic.backtrace.is_empty() {
        for entry in diagnostic.backtrace.iter() {
            if let Some(loc) = &entry.loc {
                let loc_str = if let Some(fname) = file_name {
                    format!("{}:{}:{}", fname, loc.start.line_num, loc.start.column() + 1)
                } else {
                    format!("line {}, column {}", loc.start.line_num, loc.start.column() + 1)
                };
                output.push_str(&format!("  {}while {}, at {}{}\n",
                    style::DIM,
                    entry.text,
                    loc_str,
                    style::RESET
                ));
            } else {
                output.push_str(&format!("  {}while {}{}\n",
                    style::DIM,
                    entry.text,
                    style::RESET
                ));
            }
        }
    }
    
    // Render suggestions if present
    if !diagnostic.suggestions.is_empty() {
        output.push_str("\n");
        for suggestion in &diagnostic.suggestions {
            output.push_str(&format!("{}help:{} {}\n", 
                color::GREEN,
                style::RESET,
                suggestion.message
            ));
        }
    }
    
    // Render explanation if present
    if let Some(explanation) = &diagnostic.explanation {
        output.push_str("\n");
        output.push_str(&format!("{}note:{} {}\n", 
            style::DIM,
            style::RESET,
            explanation
        ));
    }
    
    output
}

/// Render a diagnostic without ANSI colors (for piped output)
///
/// # Arguments
/// * `diagnostic` - The diagnostic to render
/// * `file_name` - Optional file name to display in the location (if None, only line:column shown)
pub fn render_diagnostic_plain(diagnostic: &Diagnostic, file_name: Option<&str>) -> String {
    let mut output = String::new();

    // Render severity and message
    let severity_str = match diagnostic.severity {
        DiagnosticSeverity::Bug => "BUG",
        DiagnosticSeverity::Error => "error",
        DiagnosticSeverity::Warning => "warning",
        DiagnosticSeverity::Info => "info",
        DiagnosticSeverity::Hint => "hint",
    };

    // Add error code if present
    let code_str = if let Some(code) = &diagnostic.code {
        format!("[{}]", code)
    } else {
        String::new()
    };

    output.push_str(&format!("{}{}: {}\n", severity_str, code_str, diagnostic.message));

    // Render primary location
    let location_str = if let Some(fname) = file_name {
        format!("{}:{}:{}", fname, diagnostic.span.start.line_num, diagnostic.span.start.column() + 1)
    } else {
        format!("line {}, column {}", diagnostic.span.start.line_num, diagnostic.span.start.column() + 1)
    };
    output.push_str(&format!("  --> {}\n", location_str));

    // Render backtrace if present - narrative style
    if !diagnostic.backtrace.is_empty() {
        for entry in diagnostic.backtrace.iter() {
            if let Some(loc) = &entry.loc {
                let loc_str = if let Some(fname) = file_name {
                    format!("{}:{}:{}", fname, loc.start.line_num, loc.start.column() + 1)
                } else {
                    format!("line {}, column {}", loc.start.line_num, loc.start.column() + 1)
                };
                output.push_str(&format!("  while {}, at {}\n", entry.text, loc_str));
            } else {
                output.push_str(&format!("  while {}\n", entry.text));
            }
        }
    }
    
    // Render suggestions if present
    if !diagnostic.suggestions.is_empty() {
        output.push_str("\n");
        for suggestion in &diagnostic.suggestions {
            output.push_str(&format!("help: {}\n", suggestion.message));
        }
    }
    
    // Render explanation if present
    if let Some(explanation) = &diagnostic.explanation {
        output.push_str("\n");
        output.push_str(&format!("note: {}\n", explanation));
    }
    
    output
}
