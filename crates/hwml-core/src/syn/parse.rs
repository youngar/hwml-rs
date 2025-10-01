use std::rc::Rc;

use crate::common::Index;
use crate::{syn, syn::RcSyntax, syn::Syntax};
use core::fmt::{Debug, Display};
use logos::{Lexer, Logos, SpannedIter};
use std::fmt::{self, write};
use std::num::ParseIntError;
use std::ops::Range;

/// The names of the expected token types.
type Expected = &'static [&'static str];

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub enum Error {
    InvalidToken(Range<usize>),
    InvalidInteger(String),
    UnknownVariable(String),
    ParseError {
        token: Option<Token>,
        expected: Expected,
    },
    #[default]
    Other,
}

impl Error {
    fn from_lexer<'input>(lex: &mut logos::Lexer<'input, Token>) -> Self {
        Error::InvalidToken(lex.span())
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::InvalidToken(_) => write!(f, "invalid token"),
            Error::InvalidInteger(txt) => write!(f, "invalid integer '{}'", txt),
            Error::UnknownVariable(name) => write!(f, "unknown variable '{}'", name),
            Error::ParseError {token, expected} => {
                match token {
                    Some(token) => write!(f, "unexpected token {}", token),
                    None => write!(f, "unexpected end of input"),
                }?;
                match expected.len() {
                    0 => Ok(()),
                    1 => write!(f, ", expected {}", expected[0]),
                    2 => write!(f, ", expected {} or {}", expected[0], expected[1]),
                    _ => {
                        write!(f, ", expected one of {}", expected[0]);
                        for i in 1 .. expected.len() - 1 {
                            write!(f, ", {}", expected[i]);
                        }
                        write!(f, ", or {}", expected[expected.len() - 1])
                    }
                }
            }
            Error::Other => write!(f, "unknown"),
        }
    }
}

impl std::error::Error for Error {}

impl From<ParseIntError> for Error {
    fn from(err: ParseIntError) -> Self {
        use std::num::IntErrorKind::*;
        match err.kind() {
            PosOverflow | NegOverflow => Error::InvalidInteger("overflow error".to_owned()),
            _ => Error::InvalidInteger("other error".to_owned()),
        }
    }
}

type ParseResult<T> = std::result::Result<T, Error>;

#[derive(Logos, Clone, Debug, Eq, PartialEq, Hash)]
#[logos(error(Error, Error::from_lexer))]
// Whitespace
#[logos(skip r"\p{Whitespace}+")]
// Comments
#[logos(skip r"//[^\\r\\n]*")]
// Ids
#[logos(subpattern id = r"[^\p{gc=Separator}\p{gc=Control}():;]+")]
pub enum Token {
    #[token("∀", priority = 4)]
    Pi,
    #[token("λ", priority = 4)]
    Lambda,
    #[token("(", priority = 10)]
    LParen,
    #[token(")", priority = 10)]
    RParen,
    #[token("→", priority = 5)]
    Arrow,
    #[token(":", priority = 4)]
    Colon,
    #[regex(r"𝒰[0-9]+", priority = 4, callback = |lex| lex.slice()["𝒰".len()..].parse())]
    Universe(usize),
    #[regex(r"%(?&id)+", priority = 4, callback = |lex| lex.slice()["%".len()..].to_owned())]
    Variable(String),
    // Brackets, semicolons, commas, and periods should break up identifiers.
    #[regex("(?&id)", priority = 2, callback = |lex| lex.slice().to_owned())]
    Ident(String),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

struct State<'input> {
    /// The names in scope. Each new name is pushed on the end.
    names: Vec<String>,
    /// The main lexer.
    lexer: Lexer<'input, Token>,
    /// The current token. We support single token peeking.
    token: Option<ParseResult<Token>>,
}

impl<'input> State<'input> {
    fn new(input: &'input str) -> State<'input> {
        let mut lexer = Token::lexer(input);
        let token = lexer.next();
        State {
            names: Vec::new(),
            lexer,
            token,
        }
    }

    /// Peek at the current token.
    fn peek_token(&self) -> Option<ParseResult<Token>> {
        self.token.clone()
    }

    /// Advance to the next token.
    fn advance_token(&mut self) {
        self.token = self.lexer.next();
    }

    /// Push a name to the environment.
    fn push_name(&mut self, name: String) {
        self.names.push(name);
    }

    /// Find a name in the environment.
    fn find_name(&self, name: &String) -> Option<Index> {
        for (i, n) in self.names.iter().rev().enumerate() {
            if name == n {
                return Some(Index::new(i));
            }
        }
        None
    }

    /// Get the current depth of the name environment.
    fn names_depth(&self) -> usize {
        self.names.len()
    }

    /// Reset the name environment to a given depth.
    fn reset_names(&mut self, depth: usize) {
        self.names.truncate(depth);
    }
}

fn p_while0<'input, T, F>(state: &mut State<'input>, f: F) -> ParseResult<Vec<T>>
where
    F: Fn(&mut State<'input>) -> ParseResult<Option<T>>,
{
    let mut result = Vec::new();
    while let Some(t) = f(state)? {
        result.push(t);
    }
    Ok(result)
}

fn p_while1<'input, T, F>(state: &mut State<'input>, expected: Expected, f: F) -> ParseResult<Vec<T>>
where
    F: Fn(&mut State<'input>) -> ParseResult<Option<T>>,
{
    let mut result = Vec::new();
    if let Some(t) = f(state)? {
        result.push(t);
    } else {
        return Err(Error::ParseError{token: None, expected});
    }
    result.append(&mut p_while0(state, f)?);
    Ok(result)
}

fn p_token_opt<'input>(state: &mut State<'input>, token: Token) -> ParseResult<Option<()>> {
    match state.peek_token() {
        Some(Err(err)) => Err(err),
        Some(Ok(t)) if t == token => {
            state.advance_token();
            Ok(Some(()))
        }
        _ => Ok(None),
    }
}

fn p_token<'input>(state: &mut State<'input>, token: Token, expected: Expected) -> ParseResult<()> {
    match state.peek_token() {
        Some(Err(e)) => Err(e),
        Some(Ok(t)) => {
            if t == token {
                state.advance_token();
                Ok(())
            } else {
                Err(Error::ParseError { token: Some(t), expected })
            }
        }
        None => Err(Error::ParseError { token: None, expected }),
    }
}

fn p_lparen_opt(state: &mut State) -> ParseResult<Option<()>> {
    p_token_opt(state, Token::LParen)
}

fn p_rparen(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::RParen, &[")"])
}

fn p_arrow(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::Arrow, &["->"])
}

fn p_colon(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::Colon, &[])
}

fn p_colon_opt(state: &mut State) -> ParseResult<Option<()>> {
    p_token_opt(state, Token::Colon)
}

fn p_binder(state: &mut State) -> ParseResult<Option<()>> {
    match state.peek_token() {
        Some(Err(err)) => Err(err),
        Some(Ok(Token::Variable(name))) => {
            let name = name.clone();
            state.advance_token();
            state.push_name(name);
            Ok(Some(()))
        }
        Some(Ok(token)) => Err(Error::ParseError { token: Some(token), expected: &["binder"] }),
        None => Err(Error::ParseError { token: None, expected: &["binder"] }),
    }
}

fn p_binder_opt(state: &mut State) -> ParseResult<Option<()>> {
    match state.peek_token() {
        Some(Err(err)) => Err(err),
        Some(Ok(Token::Variable(name))) => {
            let name = name.clone();
            state.advance_token();
            state.push_name(name);
            Ok(Some(()))
        }
        _ => Ok(None),
    }
}

fn p_pi_binder_opt(state: &mut State) -> ParseResult<Option<RcSyntax>> {
    if let Some(()) = p_lparen_opt(state)? {
        p_binder(state)?;
        p_colon(state)?;
        let ty = p_term(state)?;
        p_rparen(state)?;
        Ok(Some(ty))
    } else {
        Ok(None)
    }
}

// Parse an atomic term (no operators)
fn p_atom<'input>(state: &mut State<'input>) -> ParseResult<Option<RcSyntax>> {
    match state.peek_token() {
        Some(Err(err)) => Err(err),
        Some(Ok(token)) => match token {
            Token::LParen => {
                state.advance_token();
                let term = p_term(state)?;
                p_rparen(state)?;
                Ok(Some(term))
            }
            Token::Lambda => {
                state.advance_token();
                let depth = state.names_depth();
                let vars = p_while1(state, &["variable"], p_binder_opt)?;
                p_arrow(state)?;
                let body = p_term(state)?;
                state.reset_names(depth);
                // Build nested lambdas from right to left
                let mut result = body;
                for _ in vars.iter().rev() {
                    result = Syntax::lambda_rc(result);
                }
                Ok(Some(result))
            }
            Token::Pi => {
                state.advance_token();
                let depth = state.names_depth();
                let vars = p_while1(state, &["variable"], p_pi_binder_opt)?;
                p_arrow(state)?;
                let target = p_term(state)?;
                state.reset_names(depth);
                // Build nested Pi types from right to left
                // For each variable, we need a source type
                // For now, we'll use a placeholder - this needs to be extended
                // to parse the full syntax: ∀(%0 : source) → target
                let mut result = target;
                for ty in vars.iter().rev() {
                    result = Syntax::pi_rc(ty.clone(), result);
                }
                Ok(Some(result))
            }
            Token::Variable(name) => {
                state.advance_token();
                // Otherwise, look it up in the environment
                match state.find_name(&name) {
                    Some(index) => Ok(Some(Syntax::variable_rc(index))),
                    _ => Err(Error::UnknownVariable(name)),
                }
            }
            Token::Universe(level) => {
                state.advance_token();
                Ok(Some(Syntax::universe_rc(crate::common::UniverseLevel(
                    level as u32,
                ))))
            }
            _ => Ok(None),
        },
        None => Ok(None),
    }
}

// Parse application (left-associative): a b c => (a b) c
fn p_application<'input>(state: &mut State<'input>) -> ParseResult<Option<RcSyntax>> {
    let first = p_atom(state)?;
    if first.is_none() {
        return Ok(None);
    }

    let mut result = first.unwrap();

    // Keep parsing atoms and building left-associative applications
    while let Some(arg) = p_atom(state)? {
        result = Syntax::application_rc(result, arg);
    }

    Ok(Some(result))
}

// Parse check (type annotation): term : type
fn p_check<'input>(state: &mut State<'input>) -> ParseResult<Option<RcSyntax>> {
    let term = p_application(state)?;
    if term.is_none() {
        return Ok(None);
    }

    let term = term.unwrap();

    // Check if there's a colon
    if let Some(()) = p_colon_opt(state)? {
        Ok(Some(Syntax::check_rc(p_term(state)?, term)))
    } else {
        Ok(Some(term))
    }
}

fn p_term_opt<'input>(state: &mut State<'input>) -> ParseResult<Option<RcSyntax>> {
    p_check(state)
}

fn p_term<'input>(state: &mut State<'input>) -> ParseResult<RcSyntax> {
    match p_term_opt(state) {
        Err(err) => Err(err),
        Ok(None) => Err(Error::ParseError{token: None, expected: &["term"]}),
        Ok(Some(term)) => Ok(term),
    }
}

pub fn parse_syntax<'input>(input: &'input str) -> ParseResult<RcSyntax> {
    p_term(&mut State::new(input))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::Index;

    #[test]
    fn test_parse_lambda_single_var() {
        // Test parsing: λ %0 → %0
        let input = "λ %0 → %0";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse lambda: {:?}", result);

        let syntax = result.unwrap();

        // Should be a Lambda node
        match &*syntax {
            Syntax::Lambda(lambda) => {
                // Body should be a variable with index 0
                match &*lambda.body {
                    Syntax::Variable(var) => {
                        assert_eq!(var.index, Index::new(0));
                    }
                    other => panic!("Expected Variable in lambda body, got {:?}", other),
                }
            }
            other => panic!("Expected Lambda, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_lambda_multiple_vars() {
        // Test parsing: λ %x %y → %x
        // This creates nested lambdas: λ %x → (λ %y → %x)
        // In the innermost body, %x has index 1 (skip over %y to reach %x)
        let input = "λ %x %y → %x";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse lambda: {:?}", result);

        let syntax = result.unwrap();

        // Should be a nested Lambda (λ %x → λ %y → %x)
        match &*syntax {
            Syntax::Lambda(outer_lambda) => match &*outer_lambda.body {
                Syntax::Lambda(inner_lambda) => match &*inner_lambda.body {
                    Syntax::Variable(var) => {
                        // %x is at index 1 because we need to skip over %y (index 0)
                        assert_eq!(var.index, Index::new(1));
                    }
                    other => panic!("Expected Variable in inner lambda body, got {:?}", other),
                },
                other => panic!("Expected nested Lambda, got {:?}", other),
            },
            other => panic!("Expected Lambda, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_lambda_with_parens() {
        // Test parsing: (λ %0 → %0)
        let input = "(λ %0 → %0)";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse lambda with parens: {:?}",
            result
        );

        let syntax = result.unwrap();

        match &*syntax {
            Syntax::Lambda(lambda) => match &*lambda.body {
                Syntax::Variable(var) => {
                    assert_eq!(var.index, Index::new(0));
                }
                other => panic!("Expected Variable, got {:?}", other),
            },
            other => panic!("Expected Lambda, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_pi_simple() {
        // Test parsing: ∀(%x : 𝒰0) → 𝒰0
        // Pi binders require parentheses and a type annotation
        let input = "∀(%x : 𝒰0) → 𝒰0";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse pi: {:?}", result);

        let syntax = result.unwrap();

        // Should be a Pi node
        match &*syntax {
            Syntax::Pi(pi) => {
                // Source should be Universe(0)
                match &*pi.source {
                    Syntax::Universe(univ) => {
                        assert_eq!(univ.level, crate::common::UniverseLevel(0));
                    }
                    other => panic!("Expected Universe in pi source, got {:?}", other),
                }
                // Target should be Universe(0)
                match &*pi.target {
                    Syntax::Universe(univ) => {
                        assert_eq!(univ.level, crate::common::UniverseLevel(0));
                    }
                    other => panic!("Expected Universe in pi target, got {:?}", other),
                }
            }
            other => panic!("Expected Pi, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_universe() {
        // Test parsing: 𝒰0
        let input = "𝒰0";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse universe: {:?}", result);

        let syntax = result.unwrap();

        match &*syntax {
            Syntax::Universe(univ) => {
                assert_eq!(univ.level, crate::common::UniverseLevel(0));
            }
            other => panic!("Expected Universe, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_pi_multiple_vars() {
        // Test parsing: ∀(%x : 𝒰0) (%y : 𝒰0) → %x
        // This creates nested Pi types: ∀(%x : 𝒰0) → ∀(%y : 𝒰0) → %x
        let input = "∀(%x : 𝒰0) (%y : 𝒰0) → %x";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse pi: {:?}", result);

        let syntax = result.unwrap();

        // Should be a nested Pi (∀(%x : 𝒰0) → ∀(%y : 𝒰0) → %x)
        match &*syntax {
            Syntax::Pi(outer_pi) => {
                // Outer source should be Universe(0)
                match &*outer_pi.source {
                    Syntax::Universe(univ) => {
                        assert_eq!(univ.level, crate::common::UniverseLevel(0));
                    }
                    other => panic!("Expected Universe in outer pi source, got {:?}", other),
                }
                // Outer target should be another Pi
                match &*outer_pi.target {
                    Syntax::Pi(inner_pi) => {
                        // Inner source should be Universe(0)
                        match &*inner_pi.source {
                            Syntax::Universe(univ) => {
                                assert_eq!(univ.level, crate::common::UniverseLevel(0));
                            }
                            other => {
                                panic!("Expected Universe in inner pi source, got {:?}", other)
                            }
                        }
                        // Inner target should be a variable with index 1 (referring to %x)
                        match &*inner_pi.target {
                            Syntax::Variable(var) => {
                                assert_eq!(var.index, Index::new(1));
                            }
                            other => {
                                panic!("Expected Variable in inner pi target, got {:?}", other)
                            }
                        }
                    }
                    other => panic!("Expected nested Pi, got {:?}", other),
                }
            }
            other => panic!("Expected Pi, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_application_simple() {
        // Test parsing: (λ %f %x → %f %x) applied within a lambda context
        // We need variables to be bound, so we use a lambda expression
        let input = "λ %f %x → %f %x";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse application: {:?}", result);

        let syntax = result.unwrap();

        // Should be Lambda(Lambda(Application(%f, %x)))
        match &*syntax {
            Syntax::Lambda(outer_lambda) => match &*outer_lambda.body {
                Syntax::Lambda(inner_lambda) => match &*inner_lambda.body {
                    Syntax::Application(app) => {
                        // Function should be %f (index 1, skipping %x)
                        match &*app.function {
                            Syntax::Variable(var) => {
                                assert_eq!(var.index, Index::new(1));
                            }
                            other => panic!("Expected Variable in function, got {:?}", other),
                        }
                        // Argument should be %x (index 0)
                        match &*app.argument {
                            Syntax::Variable(var) => {
                                assert_eq!(var.index, Index::new(0));
                            }
                            other => panic!("Expected Variable in argument, got {:?}", other),
                        }
                    }
                    other => panic!("Expected Application, got {:?}", other),
                },
                other => panic!("Expected inner Lambda, got {:?}", other),
            },
            other => panic!("Expected outer Lambda, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_application_left_associative() {
        // Test parsing: λ %f %x %y → %f %x %y
        // This should parse as: λ %f → λ %x → λ %y → ((%f %x) %y)
        // Application is left-associative
        let input = "λ %f %x %y → %f %x %y";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse application: {:?}", result);

        let syntax = result.unwrap();

        // Navigate through the nested lambdas to the application
        match &*syntax {
            Syntax::Lambda(lambda_f) => match &*lambda_f.body {
                Syntax::Lambda(lambda_x) => match &*lambda_x.body {
                    Syntax::Lambda(lambda_y) => {
                        // Body should be Application(Application(%f, %x), %y)
                        match &*lambda_y.body {
                            Syntax::Application(outer_app) => {
                                // Outer argument should be %y (index 0)
                                match &*outer_app.argument {
                                    Syntax::Variable(var) => {
                                        assert_eq!(var.index, Index::new(0));
                                    }
                                    other => {
                                        panic!(
                                            "Expected Variable %y in outer argument, got {:?}",
                                            other
                                        )
                                    }
                                }
                                // Outer function should be Application(%f, %x)
                                match &*outer_app.function {
                                    Syntax::Application(inner_app) => {
                                        // Inner function should be %f (index 2)
                                        match &*inner_app.function {
                                            Syntax::Variable(var) => {
                                                assert_eq!(var.index, Index::new(2));
                                            }
                                            other => {
                                                panic!("Expected Variable %f, got {:?}", other)
                                            }
                                        }
                                        // Inner argument should be %x (index 1)
                                        match &*inner_app.argument {
                                            Syntax::Variable(var) => {
                                                assert_eq!(var.index, Index::new(1));
                                            }
                                            other => {
                                                panic!("Expected Variable %x, got {:?}", other)
                                            }
                                        }
                                    }
                                    other => panic!("Expected nested Application, got {:?}", other),
                                }
                            }
                            other => panic!("Expected Application, got {:?}", other),
                        }
                    }
                    other => panic!("Expected lambda %y, got {:?}", other),
                },
                other => panic!("Expected lambda %x, got {:?}", other),
            },
            other => panic!("Expected lambda %f, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_check() {
        // Test parsing: (λ %x → %x) : 𝒰0
        // We need a complete term to check, so we use a lambda
        let input = "(λ %x → %x) : 𝒰0";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse check: {:?}", result);

        let syntax = result.unwrap();

        // Should be a Check node
        match &*syntax {
            Syntax::Check(check) => {
                // Term should be a Lambda
                match &*check.term {
                    Syntax::Lambda(lambda) => match &*lambda.body {
                        Syntax::Variable(var) => {
                            assert_eq!(var.index, Index::new(0));
                        }
                        other => panic!("Expected Variable in lambda body, got {:?}", other),
                    },
                    other => panic!("Expected Lambda in term, got {:?}", other),
                }
                // Type should be Universe(0)
                match &*check.ty {
                    Syntax::Universe(univ) => {
                        assert_eq!(univ.level, crate::common::UniverseLevel(0));
                    }
                    other => panic!("Expected Universe in type, got {:?}", other),
                }
            }
            other => panic!("Expected Check, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_check_with_application() {
        // Test parsing: (λ %f %x → %f %x) : 𝒰0
        // Should parse as Check(Lambda(Lambda(Application(%f, %x))), Universe(0))
        let input = "(λ %f %x → %f %x) : 𝒰0";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse check with application: {:?}",
            result
        );

        let syntax = result.unwrap();

        // Should be Check(Lambda(Lambda(Application(%f, %x))), Universe(0))
        match &*syntax {
            Syntax::Check(check) => {
                // Term should be nested Lambdas with Application
                match &*check.term {
                    Syntax::Lambda(outer_lambda) => match &*outer_lambda.body {
                        Syntax::Lambda(inner_lambda) => match &*inner_lambda.body {
                            Syntax::Application(app) => {
                                // Function should be %f (index 1)
                                match &*app.function {
                                    Syntax::Variable(var) => {
                                        assert_eq!(var.index, Index::new(1));
                                    }
                                    other => panic!("Expected Variable %f, got {:?}", other),
                                }
                                // Argument should be %x (index 0)
                                match &*app.argument {
                                    Syntax::Variable(var) => {
                                        assert_eq!(var.index, Index::new(0));
                                    }
                                    other => panic!("Expected Variable %x, got {:?}", other),
                                }
                            }
                            other => {
                                panic!("Expected Application in inner lambda, got {:?}", other)
                            }
                        },
                        other => panic!("Expected inner Lambda, got {:?}", other),
                    },
                    other => panic!("Expected outer Lambda in term, got {:?}", other),
                }
                // Type should be Universe(0)
                match &*check.ty {
                    Syntax::Universe(univ) => {
                        assert_eq!(univ.level, crate::common::UniverseLevel(0));
                    }
                    other => panic!("Expected Universe in type, got {:?}", other),
                }
            }
            other => panic!("Expected Check, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_lambda_application() {
        // Test parsing: λ %x → (λ %y → %y) %x
        // This applies an inner lambda to a bound variable
        let input = "λ %x → (λ %y → %y) %x";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse lambda application: {:?}",
            result
        );

        let syntax = result.unwrap();

        // Should be Lambda(Application(Lambda(%y), %x))
        match &*syntax {
            Syntax::Lambda(outer_lambda) => match &*outer_lambda.body {
                Syntax::Application(app) => {
                    // Function should be Lambda(%y → %y)
                    match &*app.function {
                        Syntax::Lambda(inner_lambda) => match &*inner_lambda.body {
                            Syntax::Variable(var) => {
                                assert_eq!(var.index, Index::new(0));
                            }
                            other => panic!("Expected Variable in lambda body, got {:?}", other),
                        },
                        other => panic!("Expected Lambda in function, got {:?}", other),
                    }
                    // Argument should be %x (index 0 in outer lambda context)
                    match &*app.argument {
                        Syntax::Variable(var) => {
                            assert_eq!(var.index, Index::new(0));
                        }
                        other => panic!("Expected Variable in argument, got {:?}", other),
                    }
                }
                other => panic!("Expected Application, got {:?}", other),
            },
            other => panic!("Expected outer Lambda, got {:?}", other),
        }
    }
}
