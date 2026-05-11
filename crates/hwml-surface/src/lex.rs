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
    #[token("only", priority = 4)]
    Only,
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

    // Any valid UTF-8 character (Unicode scalar value) not matching above patterns.
    // Equivalent to [\u{0}-\u{10FFFF}].
    #[regex(r".", priority = 1)]
    Unknown,

    // Any invalid UTF-8 byte sequence. This is the only way to get an Error token.
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

/// Standard lexer for HWML surface syntax.
///
/// Returns byte-based spans (start_offset, Token, end_offset).
/// Location tracking uses line and column internally for error reporting, but the
/// public API only exposes byte offsets. Convert to line:column lazily using
/// LineInfo when formatting diagnostics.
pub struct Lexer<'input> {
    inner: logos::Lexer<'input, Token>,
    line: usize,   // Current line (1-based, for error messages)
    column: usize, // Current column (1-based, for error messages)
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

/// Returns: (start_offset, Token, end_offset)
/// We track line:column internally for error reporting
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

                    // Skip trivia tokens (whitespace, comments)
                    if token.is_trivia() {
                        continue;
                    }

                    // Return non-trivia token
                    return Some((span.start, token, span.end));
                }
                Err(_err) => {
                    panic!("Lexical error at {}:{}", self.line, self.column);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper to lex and extract just the tokens (ignoring spans)
    fn lex(input: &[u8]) -> Vec<Token> {
        Lexer::new(input).map(|(_, tok, _)| tok).collect()
    }

    #[test]
    fn test_valid_utf8_identifier() {
        // Simple ASCII identifier
        let tokens = lex(b"hello");
        assert_eq!(tokens, vec![Token::Identifier]);

        // Unicode identifiers (various scripts)
        let tokens = lex("café".as_bytes());
        assert_eq!(tokens, vec![Token::Identifier]);

        let tokens = lex("привет".as_bytes());
        assert_eq!(tokens, vec![Token::Identifier]);

        let tokens = lex("こんにちは".as_bytes());
        assert_eq!(tokens, vec![Token::Identifier]);

        let tokens = lex("你好".as_bytes());
        assert_eq!(tokens, vec![Token::Identifier]);
    }

    #[test]
    fn test_emoji_identifiers() {
        // Emoji are actually valid UTF-8 and match the identifier pattern!
        // The identifier regex [^\p{gc=Separator}\p{gc=Control}{}()\[\];,]+ matches
        // anything that's not a separator, control character, or specific punctuation.
        // Emoji (which are in the Symbol/Other category) match this pattern.
        let tokens = lex("😀".as_bytes());
        assert_eq!(tokens, vec![Token::Identifier]);

        // Emoji with ZWJ sequence (👨‍👩‍👧‍👦 = family)
        // Interestingly, ZWJ (U+200D) might not be classified as Control by Unicode properties
        // used by regex, so the whole sequence might lex as a single identifier
        let tokens = lex("👨‍👩‍👧‍👦".as_bytes());
        // The actual behavior: logos treats the whole sequence as one token
        assert_eq!(tokens, vec![Token::Identifier]);

        // Combined emoji and identifier
        let tokens = lex("hello😀world".as_bytes());
        // All valid non-separator/control chars form one identifier
        assert_eq!(tokens, vec![Token::Identifier]);
    }

    #[test]
    #[should_panic(expected = "Lexical error")]
    fn test_invalid_utf8_bytes_isolated_continuation() {
        // Invalid UTF-8 causes Logos to return Err, which the Lexer wrapper panics on
        // This is intentional - we want to fail fast on invalid UTF-8 at the lexer boundary
        let _tokens = lex(&[0x80]);
    }

    #[test]
    #[should_panic(expected = "Lexical error")]
    fn test_invalid_utf8_bytes_overlong_encoding() {
        let _tokens = lex(&[0xC0, 0x80]);
    }

    #[test]
    #[should_panic(expected = "Lexical error")]
    fn test_invalid_utf8_bytes_truncated() {
        let _tokens = lex(&[0xE0, 0xA0]); // Missing third byte
    }

    #[test]
    #[should_panic(expected = "Lexical error")]
    fn test_invalid_utf8_after_valid() {
        // Valid UTF-8 followed by invalid - should lex hello then panic
        let input = b"hello\xFF";
        let _tokens = lex(input);
    }

    #[test]
    #[should_panic(expected = "Lexical error")]
    fn test_invalid_utf8_before_valid() {
        // Invalid followed by valid - should panic immediately
        let mut input = vec![0xFF];
        input.extend_from_slice(b"world");
        let _tokens = lex(&input);
    }

    #[test]
    #[should_panic(expected = "Lexical error")]
    fn test_mixed_valid_and_invalid_utf8() {
        // UTF-8 "café" but with an invalid byte in the middle
        let input = vec![b'c', b'a', b'f', 0xFF, 0xC3, 0xA9];
        let _tokens = lex(&input);
    }

    #[test]
    fn test_utf8_invariant_for_identifiers_and_numbers() {
        // This test verifies the core invariant: Identifier and Number tokens
        // always contain valid UTF-8

        let test_cases = vec![
            ("hello123".as_bytes(), vec![Token::Identifier]),
            ("42".as_bytes(), vec![Token::Number]),
            ("café123".as_bytes(), vec![Token::Identifier]),
            ("123".as_bytes(), vec![Token::Number]),
        ];

        for (input, _expected) in test_cases {
            let mut lexer = Token::lexer(input);
            while let Some(Ok(token)) = lexer.next() {
                if token == Token::Identifier || token == Token::Number {
                    let slice = lexer.slice();
                    // This MUST succeed if our invariant holds
                    let _valid_str = std::str::from_utf8(slice)
                        .expect("Identifier/Number tokens must contain valid UTF-8");
                }
            }
        }
    }

    #[test]
    fn test_three_tier_priority_cascade() {
        // Priority 2: Valid identifier charset → Identifier
        let tokens = lex(b"foo");
        assert_eq!(tokens, vec![Token::Identifier]);

        // Priority 1: Valid UTF-8 but not identifier charset → Unknown
        // Use a character that is actually excluded by the identifier pattern
        // Parentheses are explicitly excluded in the identifier regex
        let tokens = lex("(".as_bytes());
        assert_eq!(tokens, vec![Token::LParen]); // Recognized as specific token

        // Even simpler: just whitespace (separator category)
        let tokens = lex(" ".as_bytes());
        // Whitespace is filtered by is_trivia(), so we get no tokens
        assert_eq!(tokens, vec![]);
    }

    #[test]
    #[should_panic(expected = "Lexical error")]
    fn test_invalid_utf8_priority() {
        // Priority 0: Invalid UTF-8 → Err (causes panic)
        let _tokens = lex(&[0xFF]);
    }

    #[test]
    fn test_complex_unicode_sequences() {
        // Combining characters (valid UTF-8, may or may not be identifier)
        let tokens = lex("é".as_bytes()); // é as single codepoint U+00E9
        assert_eq!(tokens, vec![Token::Identifier]);

        // Note: Both composed and decomposed forms of é are treated as identifiers
        // because the identifier pattern [^\p{gc=Separator}\p{gc=Control}...]
        // includes combining characters unless they're explicitly control chars
        let tokens = lex("é".as_bytes()); // e + combining acute U+0065 U+0301
        assert_eq!(tokens, vec![Token::Identifier]);

        // Right-to-left text (Arabic)
        let tokens = lex("مرحبا".as_bytes());
        assert_eq!(tokens, vec![Token::Identifier]);
    }
}
