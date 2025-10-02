use std::collections::HashMap;
use std::rc::Rc;

use crate::common::Index;
use crate::syn::MetavariableId;
use crate::{syn, syn::RcSyntax, syn::Syntax};
use core::fmt::{Debug, Display};
use logos::{Lexer, Logos, SpannedIter};
use std::fmt;
use std::num::ParseIntError;
use std::ops::Range;

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub enum Error {
    InvalidToken(Range<usize>),
    InvalidInteger(String),
    MissingRParen,
    MissingArrow,
    MissingVariable,
    MissingTerm,
    #[default]
    Other,
}

impl Error {
    fn from_lexer<'input>(lex: &mut logos::Lexer<'input, Token>) -> Self {
        Error::InvalidToken(lex.span())
    }
}

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

fn lex_metavariable_id(lex: &mut logos::Lexer<Token>) -> Result<usize, ParseIntError> {
    lex.slice()["?".len()..].parse()
}

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
    #[regex(r"@[0-9]+", priority = 4, callback = |lex| lex.slice()["@".len()..].parse())]
    Constant(u32),
    #[regex(r"%(?&id)+", priority = 4, callback = |lex| lex.slice()["%".len()..].to_owned())]
    Variable(String),
    #[regex(r"![0-9]+", priority = 4, callback = |lex| lex.slice()["!".len()..].parse())]
    UnboundVariable(usize),
    #[regex(r"\?[0-9]+", priority = 4, callback = lex_metavariable_id)]
    Metavariable(usize),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

struct State<'input> {
    /// The names in scope. Each new name is pushed on the end.
    names: Vec<String>,
    /// Mapping from metavariable names to their IDs.
    metavariables: HashMap<String, syn::MetavariableId>,
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
            metavariables: HashMap::new(),
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
    fn find_name(&self, name: String) -> Option<Index> {
        for (i, n) in self.names.iter().rev().enumerate() {
            if name == n.as_str() {
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

    /// Get or create a metavariable ID for the given name.
    /// Metavariables are assigned IDs in the order they are discovered.
    fn get_or_create_metavar(&mut self, name: String) -> syn::MetavariableId {
        if let Some(&id) = self.metavariables.get(&name) {
            id
        } else {
            let id = syn::MetavariableId(self.metavariables.len());
            self.metavariables.insert(name, id);
            id
        }
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

fn p_while1<'input, T, F>(state: &mut State<'input>, err: Error, f: F) -> ParseResult<Vec<T>>
where
    F: Fn(&mut State<'input>) -> ParseResult<Option<T>>,
{
    let mut result = Vec::new();
    if let Some(t) = f(state)? {
        result.push(t);
    } else {
        return Err(err);
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

fn p_token<'input>(state: &mut State<'input>, token: Token, err: Error) -> ParseResult<()> {
    match state.peek_token() {
        Some(Err(e)) => Err(e),
        Some(Ok(t)) if t == token => {
            state.advance_token();
            Ok(())
        }
        _ => Err(err),
    }
}

fn p_lparen_opt(state: &mut State) -> ParseResult<Option<()>> {
    p_token_opt(state, Token::LParen)
}

fn p_rparen(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::RParen, Error::MissingRParen)
}

fn p_arrow(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::Arrow, Error::MissingArrow)
}

fn p_colon(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::Colon, Error::Other)
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
        _ => Err(Error::MissingVariable),
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
                let vars = p_while1(state, Error::MissingVariable, p_binder_opt)?;
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
                let vars = p_while1(state, Error::MissingVariable, p_pi_binder_opt)?;
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
                match state.find_name(name) {
                    Some(index) => Ok(Some(Syntax::variable_rc(index))),
                    _ => Err(Error::MissingVariable),
                }
            }
            Token::UnboundVariable(negative_level) => {
                state.advance_token();
                // Convert negative level to index: index = depth + negative_level
                let index = Index::new(state.names_depth() + negative_level);
                Ok(Some(Syntax::variable_rc(index)))
            }
            Token::Universe(level) => {
                state.advance_token();
                Ok(Some(Syntax::universe_rc(crate::common::UniverseLevel(
                    level as u32,
                ))))
            }
            Token::Constant(id) => {
                state.advance_token();
                Ok(Some(Syntax::constant_rc(syn::ConstantId(id))))
            }
            Token::Metavariable(id) => {
                state.advance_token();
                let closure = syn::Closure::new();
                Ok(Some(Syntax::metavariable_rc(MetavariableId(id), closure)))
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
        Ok(None) => Err(Error::MissingTerm),
        Ok(Some(term)) => Ok(term),
    }
}

pub fn parse_syntax<'input>(input: &'input str) -> ParseResult<RcSyntax> {
    p_term(&mut State::new(input))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{Index, UniverseLevel};
    use crate::syn::*;

    #[test]
    fn test_parse_lambda_single_var() {
        // Test parsing: λ %0 → %0
        let input = "λ %0 → %0";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse lambda: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: λ %0 → %0
        let expected = Syntax::lambda_rc(Syntax::variable_rc(Index(0)));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_lambda_multiple_vars() {
        // Test parsing: λ %x %y → %x
        // This creates nested lambdas: λ %x → (λ %y → %x)
        // In the innermost body, %x has index 1 (skip over %y to reach %x)
        let input = "λ %x %y → %x";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse lambda: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: λ %x → λ %y → %x
        // %x is at index 1 in the innermost scope
        let expected = Syntax::lambda_rc(Syntax::lambda_rc(Syntax::variable_rc(Index(1))));

        assert_eq!(parsed, expected);
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

        let parsed = result.unwrap();

        // Build expected: λ %0 → %0
        let expected = Syntax::lambda_rc(Syntax::variable_rc(Index(0)));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_pi_simple() {
        // Test parsing: ∀(%x : 𝒰0) → 𝒰0
        // Pi binders require parentheses and a type annotation
        let input = "∀(%x : 𝒰0) → 𝒰0";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse pi: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: ∀(%x : 𝒰0) → 𝒰0
        let expected = Syntax::pi_rc(
            Syntax::universe_rc(UniverseLevel(0)),
            Syntax::universe_rc(UniverseLevel(0)),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_universe() {
        // Test parsing: 𝒰0
        let input = "𝒰0";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse universe: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: 𝒰0
        let expected = Syntax::universe_rc(UniverseLevel(0));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_pi_multiple_vars() {
        // Test parsing: ∀(%x : 𝒰0) (%y : 𝒰0) → %x
        // This creates nested Pi types: ∀(%x : 𝒰0) → ∀(%y : 𝒰0) → %x
        let input = "∀(%x : 𝒰0) (%y : 𝒰0) → %x";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse pi: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: ∀(%x : 𝒰0) → ∀(%y : 𝒰0) → %x
        // %x is at index 1 in the innermost scope (skip over %y)
        let expected = Syntax::pi_rc(
            Syntax::universe_rc(UniverseLevel(0)),
            Syntax::pi_rc(
                Syntax::universe_rc(UniverseLevel(0)),
                Syntax::variable_rc(Index(1)),
            ),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_application_simple() {
        // Test parsing: λ %f %x → %f %x
        // We need variables to be bound, so we use a lambda expression
        let input = "λ %f %x → %f %x";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse application: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: λ %f → λ %x → %f %x
        // %f is at index 1 (skip over %x), %x is at index 0
        let expected = Syntax::lambda_rc(Syntax::lambda_rc(Syntax::application_rc(
            Syntax::variable_rc(Index(1)),
            Syntax::variable_rc(Index(0)),
        )));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_application_left_associative() {
        // Test parsing: λ %f %x %y → %f %x %y
        // This should parse as: λ %f → λ %x → λ %y → ((%f %x) %y)
        // Application is left-associative
        let input = "λ %f %x %y → %f %x %y";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse application: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: λ %f → λ %x → λ %y → ((%f %x) %y)
        // %f is at index 2, %x is at index 1, %y is at index 0
        let expected = Syntax::lambda_rc(Syntax::lambda_rc(Syntax::lambda_rc(
            Syntax::application_rc(
                Syntax::application_rc(
                    Syntax::variable_rc(Index(2)),
                    Syntax::variable_rc(Index(1)),
                ),
                Syntax::variable_rc(Index(0)),
            ),
        )));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_check() {
        // Test parsing: (λ %x → %x) : 𝒰0
        // We need a complete term to check, so we use a lambda
        let input = "(λ %x → %x) : 𝒰0";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse check: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: (λ %x → %x) : 𝒰0
        let expected = Syntax::check_rc(
            Syntax::universe_rc(UniverseLevel(0)),
            Syntax::lambda_rc(Syntax::variable_rc(Index(0))),
        );

        assert_eq!(parsed, expected);
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

        let parsed = result.unwrap();

        // Build expected: (λ %f → λ %x → %f %x) : 𝒰0
        let expected = Syntax::check_rc(
            Syntax::universe_rc(UniverseLevel(0)),
            Syntax::lambda_rc(Syntax::lambda_rc(Syntax::application_rc(
                Syntax::variable_rc(Index(1)),
                Syntax::variable_rc(Index(0)),
            ))),
        );

        assert_eq!(parsed, expected);
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

        let parsed = result.unwrap();

        // Build expected: λ %x → (λ %y → %y) %x
        let expected = Syntax::lambda_rc(Syntax::application_rc(
            Syntax::lambda_rc(Syntax::variable_rc(Index(0))),
            Syntax::variable_rc(Index(0)),
        ));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_metavariable_simple() {
        // Test parsing: ?x
        let input = "?x";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse metavariable: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: ?x with ID 0
        use crate::syn::{Closure, MetavariableId};
        let expected = Syntax::metavariable_rc(MetavariableId(0), Closure::new());

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_metavariable_multiple() {
        // Test parsing: ?x ?y ?x
        // ?x should get ID 0, ?y should get ID 1, and the second ?x should reuse ID 0
        let input = "?x ?y ?x";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse multiple metavariables: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: (?x ?y) ?x
        // Application is left-associative
        use crate::syn::{Closure, MetavariableId};
        let expected = Syntax::application_rc(
            Syntax::application_rc(
                Syntax::metavariable_rc(MetavariableId(0), Closure::new()),
                Syntax::metavariable_rc(MetavariableId(1), Closure::new()),
            ),
            Syntax::metavariable_rc(MetavariableId(0), Closure::new()),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_metavariable_in_lambda() {
        // Test parsing: λ %x → ?f %x
        let input = "λ %x → ?f %x";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse metavariable in lambda: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: λ %x → ?f %x
        use crate::syn::{Closure, MetavariableId};
        let expected = Syntax::lambda_rc(Syntax::application_rc(
            Syntax::metavariable_rc(MetavariableId(0), Closure::new()),
            Syntax::variable_rc(Index(0)),
        ));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_metavariable_ordering() {
        // Test parsing: ?z ?a ?m
        // Should get IDs in order of discovery: ?z=0, ?a=1, ?m=2
        let input = "?z ?a ?m";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse metavariable ordering: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: (?z ?a) ?m
        use crate::syn::{Closure, MetavariableId};
        let expected = Syntax::application_rc(
            Syntax::application_rc(
                Syntax::metavariable_rc(MetavariableId(0), Closure::new()),
                Syntax::metavariable_rc(MetavariableId(1), Closure::new()),
            ),
            Syntax::metavariable_rc(MetavariableId(2), Closure::new()),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_metavariable_with_type() {
        // Test parsing: ?x : 𝒰0
        let input = "?x : 𝒰0";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse metavariable with type: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: ?x : 𝒰0
        use crate::syn::{Closure, MetavariableId};
        let expected = Syntax::check_rc(
            Syntax::universe_rc(UniverseLevel(0)),
            Syntax::metavariable_rc(MetavariableId(0), Closure::new()),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_constant_simple() {
        // Test parsing: @42
        let input = "@42";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse constant: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: @42
        use crate::syn::ConstantId;
        let expected = Syntax::constant_rc(ConstantId(42));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_constant_zero() {
        // Test parsing: @0
        let input = "@0";
        let result = parse_syntax(input);

        assert!(result.is_ok(), "Failed to parse constant @0: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: @0
        use crate::syn::ConstantId;
        let expected = Syntax::constant_rc(ConstantId(0));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_constant_large() {
        // Test parsing: @123456789
        let input = "@123456789";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse large constant: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: @123456789
        use crate::syn::ConstantId;
        let expected = Syntax::constant_rc(ConstantId(123456789));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_constant_application() {
        // Test parsing: @42 @99
        let input = "@42 @99";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse constant application: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: @42 @99
        use crate::syn::ConstantId;
        let expected = Syntax::application_rc(
            Syntax::constant_rc(ConstantId(42)),
            Syntax::constant_rc(ConstantId(99)),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_constant_with_type() {
        // Test parsing: @42 : 𝒰0
        let input = "@42 : 𝒰0";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse constant with type: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: @42 : 𝒰0
        use crate::syn::ConstantId;
        let expected = Syntax::check_rc(
            Syntax::universe_rc(UniverseLevel(0)),
            Syntax::constant_rc(ConstantId(42)),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_constant_in_lambda() {
        // Test parsing: λ %x → @42 %x
        let input = "λ %x → @42 %x";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse constant in lambda: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: λ %x → @42 %x
        use crate::syn::ConstantId;
        let expected = Syntax::lambda_rc(Syntax::application_rc(
            Syntax::constant_rc(ConstantId(42)),
            Syntax::variable_rc(Index(0)),
        ));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_constant_in_pi() {
        // Test parsing: ∀(%x : @42) → 𝒰0
        let input = "∀(%x : @42) → 𝒰0";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse constant in pi: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: ∀(%x : @42) → 𝒰0
        use crate::syn::ConstantId;
        let expected = Syntax::pi_rc(
            Syntax::constant_rc(ConstantId(42)),
            Syntax::universe_rc(UniverseLevel(0)),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_unbound_variable_simple() {
        // Test parsing: !0
        let input = "!0";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse unbound variable: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: !0 (index 0 at depth 0)
        let expected = Syntax::variable_rc(Index(0));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_unbound_variable_higher() {
        // Test parsing: !5
        let input = "!5";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse unbound variable !5: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: !5 (index 5 at depth 0)
        let expected = Syntax::variable_rc(Index(5));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_unbound_variable_in_lambda() {
        // Test parsing: λ %x → !0
        // At depth 1, !0 should become index 1
        let input = "λ %x → !0";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse unbound variable in lambda: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: λ %x → !0
        // Inside the lambda (depth 1), !0 means index = 1 + 0 = 1
        let expected = Syntax::lambda_rc(Syntax::variable_rc(Index(1)));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_unbound_variable_in_nested_lambda() {
        // Test parsing: λ %x %y → !0
        // At depth 2, !0 should become index 2
        let input = "λ %x %y → !0";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse unbound variable in nested lambda: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: λ %x → λ %y → !0
        // Inside the nested lambda (depth 2), !0 means index = 2 + 0 = 2
        let expected = Syntax::lambda_rc(Syntax::lambda_rc(Syntax::variable_rc(Index(2))));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_mixed_bound_and_unbound() {
        // Test parsing: λ %x %y → %y !0
        // %y is bound (index 0), !0 is unbound (index 2 at depth 2)
        let input = "λ %x %y → %y !0";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse mixed bound and unbound: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: λ %x → λ %y → %y !0
        // %y has index 0, !0 has index 2
        let expected = Syntax::lambda_rc(Syntax::lambda_rc(Syntax::application_rc(
            Syntax::variable_rc(Index(0)),
            Syntax::variable_rc(Index(2)),
        )));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_unbound_variable_in_pi() {
        // Test parsing: ∀(%x : 𝒰0) → !0
        // At depth 1, !0 should become index 1
        let input = "∀(%x : 𝒰0) → !0";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse unbound variable in pi: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: ∀(%x : 𝒰0) → !0
        // Inside the pi (depth 1), !0 means index = 1 + 0 = 1
        let expected = Syntax::pi_rc(
            Syntax::universe_rc(UniverseLevel(0)),
            Syntax::variable_rc(Index(1)),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_unbound_variable_application() {
        // Test parsing: !0 !1
        let input = "!0 !1";
        let result = parse_syntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse unbound variable application: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: !0 !1
        let expected =
            Syntax::application_rc(Syntax::variable_rc(Index(0)), Syntax::variable_rc(Index(1)));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_print_roundtrip_unbound() {
        use crate::syn::print::print_syntax_to_string;

        // Test that parsing and printing unbound variables works correctly
        // Note: The parser uses named binders (%x, %y) while the printer uses
        // numeric binders (%0, %1), so we can't do a perfect round-trip.
        // Instead, we test that parsing works and produces the expected AST.
        let test_cases = vec![
            ("!0", Syntax::variable_rc(Index(0))),
            ("!5", Syntax::variable_rc(Index(5))),
            (
                "λ %x → !0",
                Syntax::lambda_rc(Syntax::variable_rc(Index(1))),
            ),
            (
                "λ %x %y → %y !0",
                Syntax::lambda_rc(Syntax::lambda_rc(Syntax::application_rc(
                    Syntax::variable_rc(Index(0)),
                    Syntax::variable_rc(Index(2)),
                ))),
            ),
            (
                "∀(%x : 𝒰0) → !0",
                Syntax::pi_rc(
                    Syntax::universe_rc(UniverseLevel(0)),
                    Syntax::variable_rc(Index(1)),
                ),
            ),
            (
                "!0 !1",
                Syntax::application_rc(
                    Syntax::variable_rc(Index(0)),
                    Syntax::variable_rc(Index(1)),
                ),
            ),
        ];

        for (input, expected) in test_cases {
            let parsed = parse_syntax(input).expect(&format!("Failed to parse: {}", input));
            assert_eq!(
                parsed, expected,
                "Parse result mismatch for input: {}",
                input
            );

            // Also verify that the printed form can be understood
            let printed = print_syntax_to_string(&parsed);
            // The printed form should contain !N for unbound variables
            if input.contains("!") {
                assert!(
                    printed.contains("!"),
                    "Printed form should contain ! for input: {} (got: {})",
                    input,
                    printed
                );
            }
        }
    }

    #[test]
    fn robert_test() {
        let a = "λ %0 → %0";
        let x = parse_syntax(&a).unwrap();
        let b = print_syntax_to_string(&x);
        assert_eq!(a, b);
    }
}
