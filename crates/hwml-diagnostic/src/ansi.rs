//! ANSI escape code utilities for terminal output
//!
//! This module provides constants and utilities for ANSI escape sequences
//! used in terminal rendering, based on Asai's approach.

/// ANSI escape code prefix
const ESC: &str = "\x1b[";

/// ANSI escape code suffix (end)
const END: &str = "m";

/// ANSI Style Codes
pub mod style {
    use super::*;

    /// Reset all styles
    pub const RESET: &str = "\x1b[m";

    /// Bold/bright text
    pub const BOLD: &str = "\x1b[1m";

    /// Dim/faint text (for fringe decorations like line numbers)
    pub const DIM: &str = "\x1b[2m";

    /// Underline (used for highlighting ranges)
    pub const UNDERLINE: &str = "\x1b[4m";
}

/// ANSI Color Codes
pub mod color {
    use super::*;

    /// Red foreground (for Error severity)
    pub const RED: &str = "\x1b[31m";

    /// Yellow foreground (for Warning severity)
    pub const YELLOW: &str = "\x1b[33m";

    /// Green foreground (for Info severity)
    pub const GREEN: &str = "\x1b[32m";

    /// Blue foreground (for Hint severity)
    pub const BLUE: &str = "\x1b[34m";

    /// Red background with black foreground (for Bug severity - very visible!)
    pub const BUG: &str = "\x1b[41;30m";
}

/// Combined styles for common use cases
pub mod combined {
    use super::*;

    /// Red + underline (for Error highlights)
    pub const ERROR_HIGHLIGHT: &str = "\x1b[4;31m";

    /// Yellow + underline (for Warning highlights)
    pub const WARNING_HIGHLIGHT: &str = "\x1b[4;33m";

    /// Green + underline (for Info highlights)
    pub const INFO_HIGHLIGHT: &str = "\x1b[4;32m";

    /// Blue + underline (for Hint highlights)
    pub const HINT_HIGHLIGHT: &str = "\x1b[4;34m";

    /// Red background + black text + underline (for Bug highlights)
    pub const BUG_HIGHLIGHT: &str = "\x1b[4;41;30m";
}

/// Box-drawing characters for diagnostic structure
pub mod box_drawing {
    /// Top of multi-line block (backtrace/remarks)
    pub const TOP: &str = "╭";

    /// Middle of block
    pub const MIDDLE: &str = "┆";

    /// Bottom of block
    pub const BOTTOM: &str = "╯";

    /// Single-line indicator
    pub const SINGLE: &str = "ꭍ";
}

/// Special symbols used in diagnostic output
pub mod symbols {
    /// Severity marker (left of severity line)
    pub const SEVERITY: &str = "￫";

    /// File path marker
    pub const FILE: &str = "￭";

    /// Unlocated remark marker
    pub const REMARK: &str = "￮";

    /// Fixed-position message indicator
    pub const MESSAGE: &str = "^";

    /// Range begin marker (when ANSI disabled)
    pub const RANGE_BEGIN: &str = "«";

    /// Range end marker (when ANSI disabled)
    pub const RANGE_END: &str = "»";

    /// Point at end of line
    pub const POINT_EOL: &str = "‹EOL›";

    /// Point at end of file
    pub const POINT_EOF: &str = "‹EOF›";

    /// Point at arbitrary position
    pub const POINT_POS: &str = "‹POS›";
}

/// Configuration for ANSI escape code usage
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnsiMode {
    /// Full color support
    EnabledWithColor,

    /// ANSI codes for bold/underline but no colors (NO_COLOR env var set)
    EnabledWithoutColor,

    /// No ANSI codes at all (use text markers like « and »)
    Disabled,
}

impl AnsiMode {
    /// Auto-detect ANSI mode based on environment
    ///
    /// Checks:
    /// - Is output a TTY?
    /// - Is TERM set and not "dumb"?
    /// - Is NO_COLOR environment variable set?
    pub fn auto_detect() -> Self {
        use std::io::IsTerminal;

        // Check if stdout is a TTY
        if !std::io::stdout().is_terminal() {
            return AnsiMode::Disabled;
        }

        // Check TERM environment variable
        if let Ok(term) = std::env::var("TERM") {
            if term.is_empty() || term == "dumb" {
                return AnsiMode::Disabled;
            }
        } else {
            return AnsiMode::Disabled;
        }

        // Check NO_COLOR (see https://no-color.org/)
        if std::env::var("NO_COLOR").is_ok() {
            return AnsiMode::EnabledWithoutColor;
        }

        AnsiMode::EnabledWithColor
    }

    /// Check if ANSI codes are enabled at all
    pub fn is_enabled(self) -> bool {
        !matches!(self, AnsiMode::Disabled)
    }

    /// Check if colors are enabled
    pub fn has_color(self) -> bool {
        matches!(self, AnsiMode::EnabledWithColor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ansi_codes() {
        assert_eq!(style::RESET, "\x1b[m");
        assert_eq!(style::UNDERLINE, "\x1b[4m");
        assert_eq!(color::RED, "\x1b[31m");
        assert_eq!(combined::ERROR_HIGHLIGHT, "\x1b[4;31m");
    }
}
