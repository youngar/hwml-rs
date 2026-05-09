//! Marked source representation for rendering
//!
//! This module provides types for representing source code with embedded
//! diagnostic markers. Based on Asai's marked source architecture.
//!
//! The rendering process:
//! 1. Take diagnostics with byte-offset spans
//! 2. Read source from files
//! 3. Build marked source with embedded range markers
//! 4. Split into blocks (with smart splitting for large files)
//! 5. Render to terminal with ANSI or plain text

use crate::types::Span;
use std::path::PathBuf;

/// Special position markers for marks
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecialPosition {
    /// Mark is at the end of a line
    EndOfLine,
    
    /// Mark is at the end of a file
    EndOfFile,
}

/// A mark indicating the boundary or point of a diagnostic range
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Mark<Tag> {
    /// Beginning of a range
    RangeBegin(Tag),
    
    /// End of a range
    RangeEnd(Tag),
    
    /// A point (zero-width span)
    Point(Tag),
}

/// A token in a marked source line - either text or a mark
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token<Tag> {
    /// Plain source text
    String(String),
    
    /// A diagnostic mark with optional special position info
    Mark(Option<SpecialPosition>, Mark<Tag>),
}

/// A line of source code with embedded marks and attached messages
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Line<Tag> {
    /// Tags (messages) that should be displayed after this line
    pub marks: Vec<Tag>,
    
    /// The actual line content with embedded marks
    pub tokens: Vec<Token<Tag>>,
}

/// A block of consecutive source lines
///
/// Blocks are split when there are too many non-highlighted lines
/// (controlled by `block_splitting_threshold`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block<Tag> {
    /// Starting line number (1-indexed)
    pub begin_line_num: usize,
    
    /// Ending line number (1-indexed, inclusive)
    pub end_line_num: usize,
    
    /// The lines within this block
    pub lines: Vec<Line<Tag>>,
}

/// A part contains blocks from the same source file
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Part<Tag> {
    /// Source file path
    pub file: PathBuf,
    
    /// Blocks within this file
    pub blocks: Vec<Block<Tag>>,
}

/// Complete marked source representation
///
/// This is the output of the marking phase and input to the rendering phase.
pub type MarkedSource<Tag> = Vec<Part<Tag>>;

/// Configuration for building marked source
#[derive(Debug, Clone)]
pub struct MarkingConfig {
    /// Maximum consecutive non-highlighted lines in a block
    ///
    /// When this threshold is exceeded, the source is split into
    /// multiple blocks. Default: 5 (from Asai).
    pub block_splitting_threshold: usize,
    
    /// Set of line break sequences to recognize
    pub line_breaks: LineBreaks,
}

impl Default for MarkingConfig {
    fn default() -> Self {
        Self {
            block_splitting_threshold: 5,
            line_breaks: LineBreaks::Traditional,
        }
    }
}

/// Line break recognition mode
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LineBreaks {
    /// Traditional line breaks: LF, CR, CRLF
    ///
    /// Compatible with LSP and most parsers.
    Traditional,
    
    /// Unicode line breaks including VT, FF, NEL, LS, PS
    ///
    /// Full Unicode Line Breaking Algorithm support.
    Unicode,
}

impl LineBreaks {
    /// Check if a byte sequence is a line break
    pub fn is_line_break(&self, s: &str) -> bool {
        match self {
            LineBreaks::Traditional => {
                matches!(s, "\n" | "\r" | "\r\n")
            }
            LineBreaks::Unicode => {
                matches!(s, "\n" | "\r" | "\r\n" | "\x0B" | "\x0C" | "\u{0085}" | "\u{2028}" | "\u{2029}")
            }
        }
    }
}

/// Tag type for diagnostic rendering
///
/// Associates a message with a priority for overlapping ranges.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticTag {
    /// Index in the list (main message = 0, extra remarks = 1, 2, ...)
    pub index: usize,
    
    /// Whether this is the main message or an extra remark
    pub kind: TagKind,
    
    /// The message text to display
    pub text: String,
    
    /// Priority for overlapping ranges (lower = higher priority)
    pub priority: usize,
}

/// Kind of diagnostic tag
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TagKind {
    /// Main diagnostic message
    Main,
    
    /// Extra remark with index
    ExtraRemark(usize),
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_line_breaks_traditional() {
        let lb = LineBreaks::Traditional;
        assert!(lb.is_line_break("\n"));
        assert!(lb.is_line_break("\r"));
        assert!(lb.is_line_break("\r\n"));
        assert!(!lb.is_line_break("\x0B")); // VT not recognized
    }
    
    #[test]
    fn test_line_breaks_unicode() {
        let lb = LineBreaks::Unicode;
        assert!(lb.is_line_break("\n"));
        assert!(lb.is_line_break("\x0B")); // VT
        assert!(lb.is_line_break("\u{2028}")); // LS
    }
}
