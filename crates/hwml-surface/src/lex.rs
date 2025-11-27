use logos::{Logos, SpannedIter};
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
    #[token("def", priority = 4)]
    Def,
    #[token("meta", priority = 4)]
    Meta,
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
    #[token("'", priority = 5)]
    Quote,
    #[token("~", priority = 5)]
    Splice,
    #[token("^", priority = 5)]
    Raise,
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
    // Brackets, semicolons, commas, periods, quote, splice, and raise should break up identifiers.
    #[regex(r"[^\p{gc=Separator}\p{gc=Control}{}()\[\];,\.'~^]+", priority = 2)]
    Ident,
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

pub struct Lexer<'input> {
    // instead of an iterator over characters, we have a token iterator
    token_stream: SpannedIter<'input, Token>,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input [u8]) -> Self {
        // the Token::lexer() method is provided by the Logos trait
        Self {
            token_stream: Token::lexer(input).spanned(),
        }
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = (usize, Token, usize);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(result) = self.token_stream.next() {
            match result {
                (Ok(token), span) => match token.is_trivia() {
                    true => continue,
                    false => return Some((span.start, token, span.end)),
                },
                (Err(_err), _span) => panic!("invalid token"),
            }
        }
        return None;
    }
}
