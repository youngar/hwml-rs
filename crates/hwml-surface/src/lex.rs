use logos::Logos;
use std::fmt;

#[derive(Default, Debug, Clone, PartialEq)]
pub enum LexicalError {
    #[default]
    InvalidToken,
}

// See the the Unicode Standard Annex #31, Identifier and Pattern Syntax for
// information about these character classes.
#[derive(Logos, Copy, Clone, Debug, Eq, PartialEq, Hash)]
#[logos(source = [u8], error = LexicalError)]
// Vertical whitespace. See Unicode Standard Annex #14, Unicode Line Breaking Algorithm. A CR
// indicates a mandatory break after, unless followed by a LF.
// 000A LINE FEED (LF)
// 000B LINE TABULATION (VT)
// 000C FORM FEED (FF)
// 000D CARRIAGE RETURN (CR)
// 0085 NEXT LINE (NEL)
// 2028 LINE SEPARATOR (LS)
// 2029 PARAGRAPH SEPARATOR (PS)
#[logos(subpattern vertical_whitespace = "\u{000A}|\u{000B}|\u{000C}|\u{000D}|\u{0085}|\u{2028}|\u{2029}|\u{000D}\u{000A}")]
// Horizontal whitespace: space separators plus U+0009 tab. This should be equivalent to the `blank` character class, which is defined as:
// \p{Whitespace} -- [\N{LF} \N{VT} \N{FF} \N{CR} \N{NEL} \p{gc=Line_Separator} \p{gc=Paragraph_Separator}]
// Unfortunately, the rust regex crate defines blank as only "[ \t]". See https://www.unicode.org/reports/tr18/#Compatibility_Properties
// 0009 CHARACTER TABULATION (HT)
// 0020 SPACE
// 00A0 NO-BREAK SPACE
// 1680 OGHAM SPACE MARK
// 2000 EN QUAD
// 2001 EM QUAD
// 2002 EN SPACE
// 2003 EM SPACE
// 2004 THREE-PER-EM SPACE
// 2005 FOUR-PER-EM SPACE
// 2006 SIX-PER-EM SPACE
// 2007 FIGURE SPACE
// 2008 PUNCTUATION SPACE
// 2009 THIN SPACE
// 200A HAIR SPACE
// 202F NARROW NO-BREAK SPACE
// 205F MEDIUM MATHEMATICAL SPACE
// 3000 IDEOGRAPHIC SPACE
#[logos(subpattern horizontal_whitespace = "\u{0009}|\u{0020}|\u{00A0}|\u{1680}|\u{2000}|\u{2001}|\u{2002}|\u{2003}|\u{2004}|\u{2005}|\u{2006}|\u{2007}|\u{2008}|\u{2009}|\u{200A}|\u{202F}|\u{205F}|\u{3000}")]
pub enum Token {
    #[token("namespace", priority = 4)]
    Namespace,
    #[token("def", priority = 4)]
    Def,
    #[token("meta", priority = 4)]
    Meta,
    #[token("prim", priority = 4)]
    Prim,
    #[token("rassoc", priority = 4)]
    RAssoc,
    #[token("lassoc", priority = 4)]
    LAssoc,
    #[token("let", priority = 4)]
    Let,
    #[token("in", priority = 4)]
    In,
    #[token("fun", priority = 4)]
    Fun,
    #[token("match", priority = 4)]
    Match,
    #[token("with", priority = 4)]
    With,
    #[token("end", priority = 4)]
    End,
    #[token("inductive", priority = 4)]
    Inductive,
    #[token("where", priority = 4)]
    Where,
    #[token("Type", priority = 4)]
    Type,
    #[token("open", priority = 4)]
    Open,
    #[token("hiding", priority = 4)]
    Hiding,
    #[token("renaming", priority = 4)]
    Renaming,
    #[token("as", priority = 4)]
    As,
    #[token("to", priority = 4)]
    To,
    #[token("(", priority = 10)]
    LParen,
    #[token(")", priority = 10)]
    RParen,
    #[token("{", priority = 10)]
    LBrace,
    #[token("}", priority = 10)]
    RBrace,
    #[token("[", priority = 10)]
    LBrack,
    #[token("]", priority = 10)]
    RBrack,
    #[token("->", priority = 5)]
    Arrow,
    #[token("=>", priority = 5)]
    FatArrow,
    #[token("~>", priority = 5)]
    SquigglyArrow,
    #[token(":=", priority = 5)]
    ColonEqual,
    #[token(",", priority = 4)]
    Comma,
    #[token(".", priority = 4)]
    Period,
    #[token(":", priority = 4)]
    Colon,
    #[token(";", priority = 4)]
    Semicolon,
    #[token("|", priority = 4)]
    Pipe,
    #[token("_", priority = 4)]
    Underscore,
    #[regex("(?&vertical_whitespace)", priority = 4)]
    Newline,
    #[regex(r"(?&horizontal_whitespace)+", priority = 4)]
    Space,
    #[regex(r"//.*", priority = 100)]
    LineComment,
    #[regex(r"/\*[^*]*\*+(?:[^/*][^*]*\*+)*/", priority = 5)]
    BlockComment,
    #[regex(r"[0-9]+", priority = 3)]
    Number,
    // Identifiers can contain dots for qualified names like Foo.Bar.Baz
    // Brackets, semicolons, and commas should break up identifiers.
    #[regex(r"[^\p{gc=Separator}\p{gc=Control}{}()\[\];,]+", priority = 2)]
    Identifier,
    // Any valid UTF-8 character is treated as some unknown kind of whitespace.
    // Equivalent to [\u{0}-\u{10FFFF}].
    #[regex(r".", priority = 1)]
    Unknown,
    // Any invalid character is an error.
    #[regex(r"[\x00-\xFF]", priority = 0)]
    Error,
}

impl Token {
    pub fn is_trivia(&self) -> bool {
        match self {
            Token::Space
            | Token::Newline
            | Token::LineComment
            | Token::BlockComment
            | Token::Unknown => true,
            _ => false,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// A streaming lexer that tracks line:column positions natively.
///
/// Because HWML uses a **lossless grammar** (every byte is tokenized,
/// including whitespace and comments), we can track line:column positions
/// incrementally as we stream tokens with ZERO overhead - no pre-computation,
/// no lookup tables, just a simple counter that updates based on tokens consumed.
pub struct Lexer<'input> {
    inner: logos::Lexer<'input, Token>,
    line: usize,   // Current line (1-based for MLIR/CIRCT)
    column: usize, // Current column (1-based for MLIR/CIRCT)
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input [u8]) -> Self {
        Self {
            inner: Token::lexer(input),
            line: 1,
            column: 1,
        }
    }
}

/// LALRPOP expects: (start_offset, Token, end_offset)
/// We keep this interface for compatibility, but we also track line:column internally
impl<'input> Iterator for Lexer<'input> {
    type Item = (usize, Token, usize);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let token = self.inner.next()?;
            let span = self.inner.span();
            let slice = self.inner.slice();

            // Capture location at START of token (for error reporting)
            let _start_line = self.line;
            let _start_column = self.column;

            // Update line:column state based on the token we just consumed
            match token {
                Ok(Token::Newline) => {
                    self.line += 1;
                    self.column = 1;
                }
                Ok(Token::BlockComment) => {
                    // Block comments can span multiple lines - scan for newlines
                    let newlines = slice.iter().filter(|&&b| b == b'\n').count();
                    if newlines > 0 {
                        self.line += newlines;
                        // Column is distance from last newline to end of comment
                        let last_nl_idx = slice.iter().rposition(|&b| b == b'\n').unwrap();
                        self.column = slice.len() - last_nl_idx;
                    } else {
                        // No newlines - just advance column by byte count
                        self.column += slice.len();
                    }
                }
                Ok(token) => {
                    // All other tokens are single-line - just advance column
                    // Using byte count (not char count) - fine for MLIR FileLineColLoc
                    self.column += slice.len();

                    // Skip trivia tokens (whitespace, comments) for LALRPOP
                    if token.is_trivia() {
                        continue;
                    }

                    // Return non-trivia token to LALRPOP
                    return Some((span.start, token, span.end));
                }
                Err(_err) => {
                    panic!("Lexical error at {}:{}", self.line, self.column);
                }
            }
        }
    }
}

/// Extended lexer that exposes line:column positions for each token.
/// Use this when you need location information during parsing.
pub struct LocLexer<'input> {
    inner: logos::Lexer<'input, Token>,
    line: usize,
    column: usize,
}

impl<'input> LocLexer<'input> {
    pub fn new(input: &'input [u8]) -> Self {
        Self {
            inner: Token::lexer(input),
            line: 1,
            column: 1,
        }
    }
}

/// The output: (Token, byte_span, start_line, start_column)
/// All values are 1-based to match MLIR/CIRCT conventions
pub type SpannedToken = (Token, std::ops::Range<usize>, usize, usize);

impl<'input> Iterator for LocLexer<'input> {
    type Item = SpannedToken;

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.inner.next()?;
        let span = self.inner.span();
        let slice = self.inner.slice();

        // Capture location at START of token
        let out_line = self.line;
        let out_column = self.column;

        // Update state based on token consumed
        match token {
            Ok(Token::Newline) => {
                self.line += 1;
                self.column = 1;
            }
            Ok(Token::BlockComment) => {
                let newlines = slice.iter().filter(|&&b| b == b'\n').count();
                if newlines > 0 {
                    self.line += newlines;
                    let last_nl_idx = slice.iter().rposition(|&b| b == b'\n').unwrap();
                    self.column = slice.len() - last_nl_idx;
                } else {
                    self.column += slice.len();
                }
            }
            Ok(_) => {
                self.column += slice.len();
            }
            Err(_) => {
                // Still update column even on error
                self.column += slice.len();
            }
        }

        Some((token.unwrap_or(Token::Error), span, out_line, out_column))
    }
}
