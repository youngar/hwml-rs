use derive_new::new;
use logos::Logos;
use std::fmt;

pub struct StringId(pub u32);

pub struct StringStore {}

// See the the Unicode Standard Annex #31, Identifier and Pattern Syntax for
// information about these character classes.
#[derive(Logos, Copy, Clone, Debug, Eq, PartialEq, Hash, new)]
#[logos(source = [u8])]
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
pub enum TokenKind {
    #[token("def", priority = 4)]
    Def,
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
    // Brackets, semicolons, commas, and periods should break up identifiers.
    #[regex(r"[^\p{gc=Separator}\p{gc=Control}{}()\[\];,\.]+", priority = 2)]
    Ident,
    // Any valid UTF-8 character is treated as some unknown kind of whitespace.
    // Equivalent to [\u{0}-\u{10FFFF}].
    #[regex(r".", priority = 1)]
    Unknown,
    // Any invalid character is an error.
    #[regex(r"[\x00-\xFF]", priority = 0)]
    Error,
    Eof,
}

impl TokenKind {
    pub fn is_trivia(&self) -> bool {
        match self {
            TokenKind::Space
            | TokenKind::Newline
            | TokenKind::LineComment
            | TokenKind::BlockComment
            | TokenKind::Unknown => true,
            _ => false,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

type TokenSize = u32;

#[derive(Copy, Clone, Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub size: TokenSize,
}

impl Token {
    pub fn new(kind: TokenKind, size: TokenSize) -> Token {
        Token { kind, size }
    }

    pub fn is_trivia(&self) -> bool {
        self.kind.is_trivia()
    }
}

pub struct TokenIndex(pub u32);

pub struct TokenStore {
    storage: Vec<Token>,
}

impl TokenStore {
    pub fn new(storage: Vec<Token>) -> TokenStore {
        TokenStore { storage }
    }

    pub fn get(&self, index: TokenIndex) -> Token {
        self.storage[index.0 as usize]
    }
}

pub fn lex(input: &[u8]) -> la_arena::Arena<Token> {
    let mut lexer = TokenKind::lexer(input);
    let mut tokens = la_arena::Arena::new();
    while let Some(result) = lexer.next() {
        let span = lexer.span();
        let size = (span.end - span.start) as u32;
        match result {
            Ok(kind) => {
                tokens.alloc(Token::new(kind, size));
            }
            Err(error) => {
                // Since our lexer covers every possible input, we should never
                // encounter an error.
                panic!("Lexing error: {:?}", error);
            }
        }
    }

    tokens.alloc(Token::new(TokenKind::Eof, 0));
    return tokens;
}

////////////////////////////////////////////////////////////////////////////////
///
///
use lalrpop_util::lalrpop_mod;

#[derive(Eq, PartialEq, Debug, Hash, Copy, Clone, new)]
pub struct T<'input> {
    pub kind: TokenKind,
    pub str: &'input str,
}

lalrpop_mod!(
    #[allow(clippy::ptr_arg)]
    #[rustfmt::skip]
    pub grammar
);
