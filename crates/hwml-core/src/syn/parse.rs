use crate::common::{DBParseError, Index, Level, NegativeLevel};
use crate::syn::{self, HSyntax, RcHSyntax};
use crate::syn::{Closure, MetavariableId, RcSyntax, Syntax};
use core::fmt::Debug;
use logos::{Lexer, Logos};
use std::fmt;
use std::num::ParseIntError;
use std::ops::Range;

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub enum Error {
    InvalidToken(Range<usize>),
    InvalidInteger(String),
    MissingRParen,
    MissingRBracket,
    MissingArrow,
    MissingVariable,
    MissingTerm,
    UnknownVariable(String),
    DBParseError(DBParseError),
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

impl From<DBParseError> for Error {
    fn from(err: DBParseError) -> Self {
        Error::DBParseError(err)
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
#[logos(subpattern id = r"[^\p{gc=Separator}\p{gc=Control}():;,\[\]!\?\%]+")]
pub enum Token {
    #[token("∀", priority = 4)]
    Pi,
    #[token("λ", priority = 4)]
    Lambda,
    #[token("'", priority = 4)]
    Quote,
    #[token("~", priority = 4)]
    Splice,
    #[token("^", priority = 4)]
    Lift,
    #[token("(", priority = 10)]
    LParen,
    #[token(")", priority = 10)]
    RParen,
    #[token("[", priority = 10)]
    LBracket,
    #[token("]", priority = 10)]
    RBracket,
    #[token("→", priority = 5)]
    Arrow,
    #[token(":", priority = 4)]
    Colon,
    #[token(",", priority = 10)]
    Comma,
    #[regex(r"𝒰[0-9]+", priority = 4, callback = |lex| lex.slice()["𝒰".len()..].parse())]
    Universe(usize),
    #[regex(r"@[0-9]+", priority = 4, callback = |lex| lex.slice()["@".len()..].parse())]
    Constant(u32),
    #[regex(r"%(?&id)+", priority = 4, callback = |lex| lex.slice()["%".len()..].to_owned())]
    Variable(String),
    #[regex(r"![0-9]+", priority = 4, callback = |lex| lex.slice().parse())]
    UnboundVariable(NegativeLevel),
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

fn p_lbracket_opt(state: &mut State) -> ParseResult<Option<()>> {
    p_token_opt(state, Token::LBracket)
}

fn p_rbracket(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::RBracket, Error::MissingRBracket)
}

fn p_arrow(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::Arrow, Error::MissingArrow)
}

fn p_arrow_opt(state: &mut State) -> ParseResult<Option<()>> {
    p_token_opt(state, Token::Arrow)
}

fn p_colon(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::Colon, Error::Other)
}

fn p_colon_opt(state: &mut State) -> ParseResult<Option<()>> {
    p_token_opt(state, Token::Colon)
}

fn p_variable_opt(state: &mut State) -> ParseResult<Option<String>> {
    match state.peek_token() {
        Some(Err(err)) => Err(err),
        Some(Ok(Token::Variable(name))) => {
            state.advance_token();
            Ok(Some(name))
        }
        _ => Ok(None),
    }
}

fn p_variable(state: &mut State) -> ParseResult<String> {
    match p_variable_opt(state) {
        Err(e) => Err(e),
        Ok(Some(n)) => Ok(n),
        Ok(None) => Err(Error::MissingVariable),
    }
}

fn p_pi_binder_opt(state: &mut State) -> ParseResult<Option<RcSyntax>> {
    let Some(()) = p_lparen_opt(state)? else {
        return Ok(None);
    };
    let var = p_variable(state)?;
    p_colon(state)?;
    let ty = p_harrow(state)?;
    p_rparen(state)?;
    state.push_name(var);
    Ok(Some(ty))
}

fn p_closure_opt(state: &mut State) -> ParseResult<Option<Closure>> {
    let mut values = Vec::new();
    let Some(()) = p_lbracket_opt(state)? else {
        return Ok(None);
    };
    loop {
        match p_term_opt(state) {
            Ok(Some(term)) => {
                values.push(term);
                match p_token_opt(state, Token::Comma) {
                    Ok(Some(())) => continue,
                    Ok(None) => break,
                    Err(err) => return Err(err),
                }
            }
            Ok(None) => break,
            Err(err) => return Err(err),
        }
    }
    p_rbracket(state)?;
    return Ok(Some(crate::syn::Closure::with_values(values)));
}

// Parse an atomic term (no operators)
fn p_hatom_opt<'input>(state: &mut State<'input>) -> ParseResult<Option<RcHSyntax>> {
    match state.peek_token() {
        Some(Err(err)) => Err(err),
        Some(Ok(token)) => match token {
            Token::LParen => {
                state.advance_token();
                let term = p_hterm(state)?;
                p_rparen(state)?;
                Ok(Some(term))
            }
            Token::Lambda => {
                state.advance_token();
                let depth = state.names_depth();
                let mut i = 0;
                loop {
                    match p_variable_opt(state) {
                        Err(e) => return Err(e),
                        Ok(Some(var)) => {
                            i = i + 1;
                            state.push_name(var)
                        }
                        Ok(None) => break,
                    }
                }
                p_arrow(state)?;
                let body = p_happlication(state)?;
                state.reset_names(depth);
                // Build nested lambdas from right to left
                let mut result = body;
                for _ in 0..i {
                    result = HSyntax::hlambda_rc(result);
                }
                Ok(Some(result))
            }
            Token::Variable(name) => {
                state.advance_token();
                // Otherwise, look it up in the environment
                match state.find_name(&name) {
                    Some(index) => Ok(Some(HSyntax::hvariable_rc(index))),
                    _ => Err(Error::UnknownVariable(name)),
                }
            }
            Token::UnboundVariable(negative_level) => {
                state.advance_token();
                // Convert negative level to index: index = depth + negative_level
                let index = negative_level.to_index(state.names_depth());
                Ok(Some(HSyntax::hvariable_rc(index)))
            }
            Token::Constant(id) => {
                state.advance_token();
                Ok(Some(HSyntax::hconstant_rc(syn::ConstantId(id))))
            }
            Token::Splice => {
                state.advance_token();
                let tm = p_atom(state)?;
                Ok(Some(HSyntax::splice_rc(tm)))
            }
            _ => Ok(None),
        },
        None => Ok(None),
    }
}

fn p_hatom<'input>(state: &mut State<'input>) -> ParseResult<RcHSyntax> {
    match p_hatom_opt(state) {
        Err(err) => Err(err),
        Ok(None) => Err(Error::MissingTerm),
        Ok(Some(term)) => Ok(term),
    }
}

// Parse application (left-associative): a b c => (a b) c
fn p_happlication_opt<'input>(state: &mut State<'input>) -> ParseResult<Option<RcHSyntax>> {
    let first = p_hatom_opt(state)?;
    if first.is_none() {
        return Ok(None);
    }

    let mut result = first.unwrap();

    // Keep parsing atoms and building left-associative applications
    while let Some(arg) = p_hatom_opt(state)? {
        result = HSyntax::happlication_rc(result, arg);
    }

    Ok(Some(result))
}

fn p_happlication<'input>(state: &mut State<'input>) -> ParseResult<RcHSyntax> {
    match p_happlication_opt(state) {
        Ok(None) => Err(Error::MissingTerm),
        Ok(Some(term)) => Ok(term),
        Err(err) => Err(err),
    }
}

fn p_hcheck_opt<'input>(state: &mut State<'input>) -> ParseResult<Option<RcHSyntax>> {
    let term = p_happlication(state)?;

    // Check if there's a colon
    if let Some(()) = p_colon_opt(state)? {
        Ok(Some(HSyntax::hcheck_rc(p_hterm(state)?, term)))
    } else {
        Ok(Some(term))
    }
}

fn p_hterm_opt<'input>(state: &mut State<'input>) -> ParseResult<Option<RcHSyntax>> {
    p_hcheck_opt(state)
}

fn p_hterm<'input>(state: &mut State<'input>) -> ParseResult<RcHSyntax> {
    match p_hterm_opt(state) {
        Err(err) => Err(err),
        Ok(None) => Err(Error::MissingTerm),
        Ok(Some(term)) => Ok(term),
    }
}

// Parse an atomic term (no operators)
fn p_atom_opt<'input>(state: &mut State<'input>) -> ParseResult<Option<RcSyntax>> {
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
                let mut i = 0;
                loop {
                    match p_variable_opt(state) {
                        Err(e) => return Err(e),
                        Ok(Some(var)) => {
                            i = i + 1;
                            state.push_name(var)
                        }
                        Ok(None) => break,
                    }
                }
                p_arrow(state)?;
                let body = p_harrow(state)?;
                state.reset_names(depth);
                // Build nested lambdas from right to left
                let mut result = body;
                for _ in 0..i {
                    result = Syntax::lambda_rc(result);
                }
                Ok(Some(result))
            }
            Token::Pi => {
                state.advance_token();
                let depth = state.names_depth();
                let mut tys = Vec::new();
                loop {
                    match p_pi_binder_opt(state) {
                        Err(e) => return Err(e),
                        Ok(Some(ty)) => tys.push(ty),
                        Ok(None) => break,
                    }
                }
                p_arrow(state)?;
                let target = p_harrow(state)?;
                state.reset_names(depth);
                let mut result = target;
                for ty in tys.iter().rev() {
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
            Token::UnboundVariable(negative_level) => {
                state.advance_token();
                // Convert negative level to index: index = depth + negative_level
                let index = negative_level.to_index(state.names_depth());
                Ok(Some(Syntax::variable_rc(index)))
            }
            Token::Universe(level) => {
                state.advance_token();
                Ok(Some(Syntax::universe_rc(
                    crate::common::UniverseLevel::new(level),
                )))
            }
            Token::Constant(id) => {
                state.advance_token();
                Ok(Some(Syntax::constant_rc(syn::ConstantId(id))))
            }
            Token::Metavariable(id) => {
                state.advance_token();
                let closure = match p_closure_opt(state) {
                    Ok(Some(closure)) => closure,
                    Ok(None) => Closure::new(),
                    Err(err) => return Err(err),
                };
                Ok(Some(Syntax::metavariable_rc(MetavariableId(id), closure)))
            }
            Token::Lift => {
                state.advance_token();
                let tm = p_atom(state)?;
                Ok(Some(Syntax::lift_rc(tm)))
            }
            Token::Quote => {
                state.advance_token();
                let tm = p_hatom(state)?;
                Ok(Some(Syntax::quote_rc(tm)))
            }
            _ => Ok(None),
        },
        None => Ok(None),
    }
}

fn p_atom<'input>(state: &mut State<'input>) -> ParseResult<RcSyntax> {
    match p_atom_opt(state) {
        Err(err) => Err(err),
        Ok(None) => Err(Error::MissingTerm),
        Ok(Some(term)) => Ok(term),
    }
}

// Parse application (left-associative): a b c => (a b) c
fn p_application_opt<'input>(state: &mut State<'input>) -> ParseResult<Option<RcSyntax>> {
    let first = p_atom_opt(state)?;
    if first.is_none() {
        return Ok(None);
    }

    let mut result = first.unwrap();

    // Keep parsing atoms and building left-associative applications
    while let Some(arg) = p_atom_opt(state)? {
        result = Syntax::application_rc(result, arg);
    }

    Ok(Some(result))
}

fn p_harrow_opt<'input>(state: &mut State<'input>) -> ParseResult<Option<RcSyntax>> {
    let Some(term) = p_application_opt(state)? else {
        return Ok(None);
    };

    if let Some(()) = p_arrow_opt(state)? {
        Ok(Some(Syntax::harrow_rc(term, p_harrow(state)?)))
    } else {
        Ok(Some(term))
    }
}

fn p_harrow<'input>(state: &mut State<'input>) -> ParseResult<RcSyntax> {
    match p_harrow_opt(state) {
        Ok(None) => Err(Error::MissingTerm),
        Ok(Some(term)) => Ok(term),
        Err(err) => Err(err),
    }
}

// Parse check (type annotation): term : type
fn p_check_opt<'input>(state: &mut State<'input>) -> ParseResult<Option<RcSyntax>> {
    let Some(term) = p_harrow_opt(state)? else {
        return Ok(None);
    };

    // Check if there's a colon.
    if let Some(()) = p_colon_opt(state)? {
        Ok(Some(Syntax::check_rc(p_term(state)?, term)))
    } else {
        Ok(Some(term))
    }
}

fn p_term_opt<'input>(state: &mut State<'input>) -> ParseResult<Option<RcSyntax>> {
    p_check_opt(state)
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

pub fn parse_hsyntax<'input>(input: &'input str) -> ParseResult<RcHSyntax> {
    p_hterm(&mut State::new(input))
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
            Syntax::universe_rc(UniverseLevel::new(0)),
            Syntax::universe_rc(UniverseLevel::new(0)),
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
        let expected = Syntax::universe_rc(UniverseLevel::new(0));

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
            Syntax::universe_rc(UniverseLevel::new(0)),
            Syntax::pi_rc(
                Syntax::universe_rc(UniverseLevel::new(0)),
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
            Syntax::universe_rc(UniverseLevel::new(0)),
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
            Syntax::universe_rc(UniverseLevel::new(0)),
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
        let input = "?0";
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
        let input = "?0 ?1 ?0";
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
        let input = "λ %x → ?0 %x";
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
        let input = "?0 ?1 ?2";
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
        let input = "?0 : 𝒰0";
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
            Syntax::universe_rc(UniverseLevel::new(0)),
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
            Syntax::universe_rc(UniverseLevel::new(0)),
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
            Syntax::universe_rc(UniverseLevel::new(0)),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_unbound_variable_simple() {
        let input = "!0";
        let result = parse_syntax(input);
        assert!(
            result.is_ok(),
            "Failed to parse unbound variable: {:?}",
            result
        );
        let parsed = result.unwrap();
        let expected = Syntax::variable_rc(Index(0));
        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_unbound_variable_higher() {
        let input = "!4";
        let result = parse_syntax(input);
        assert!(
            result.is_ok(),
            "Failed to parse unbound variable !5: {:?}",
            result
        );
        let parsed = result.unwrap();
        let expected = Syntax::variable_rc(Index(4));
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

        // Build expected: λ %x → λ %y → !1
        // Inside the nested lambda (depth 2), !1 means index = 2 + 1 - 1 = 2
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
            Syntax::universe_rc(UniverseLevel::new(0)),
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
        use hwml_support::pp::dump_to_str;

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
                    Syntax::universe_rc(UniverseLevel::new(0)),
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
            let printed = dump_to_str(&parsed);
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

    // ========== HTERM PARSING TESTS ==========

    #[test]
    fn test_parse_hconstant_simple() {
        // Test parsing: @42
        let input = "@42";
        let result = parse_hsyntax(input);

        assert!(result.is_ok(), "Failed to parse hconstant: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: @42
        use crate::syn::ConstantId;
        let expected = HSyntax::hconstant_rc(ConstantId(42));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hconstant_zero() {
        // Test parsing: @0
        let input = "@0";
        let result = parse_hsyntax(input);

        assert!(result.is_ok(), "Failed to parse hconstant @0: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: @0
        use crate::syn::ConstantId;
        let expected = HSyntax::hconstant_rc(ConstantId(0));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hconstant_large() {
        // Test parsing: @123456789
        let input = "@123456789";
        let result = parse_hsyntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse large hconstant: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: @123456789
        use crate::syn::ConstantId;
        let expected = HSyntax::hconstant_rc(ConstantId(123456789));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hvariable_bound() {
        // Test parsing: λ %x → %x
        let input = "λ %x → %x";
        let result = parse_hsyntax(input);

        assert!(result.is_ok(), "Failed to parse hvariable: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: λ %x → %x
        let expected = HSyntax::hlambda_rc(HSyntax::hvariable_rc(Index(0)));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hvariable_unbound() {
        // Test parsing: !0
        let input = "!0";
        let result = parse_hsyntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse unbound hvariable: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: !0 (at depth 0, becomes index 0)
        let expected = HSyntax::hvariable_rc(Index(0));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hvariable_unbound_in_lambda() {
        // Test parsing: λ %x → !0
        // At depth 1, !0 should become index 1
        let input = "λ %x → !0";
        let result = parse_hsyntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse unbound hvariable in lambda: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: λ %x → !0
        // Inside the lambda (depth 1), !0 means index = 1 + 0 = 1
        let expected = HSyntax::hlambda_rc(HSyntax::hvariable_rc(Index(1)));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hlambda_single_var() {
        // Test parsing: λ %x → %x
        let input = "λ %x → %x";
        let result = parse_hsyntax(input);

        assert!(result.is_ok(), "Failed to parse hlambda: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: λ %x → %x
        let expected = HSyntax::hlambda_rc(HSyntax::hvariable_rc(Index(0)));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hlambda_multiple_vars() {
        // Test parsing: λ %x %y → %x
        // This creates nested lambdas: λ %x → (λ %y → %x)
        // In the innermost body, %x has index 1 (skip over %y to reach %x)
        let input = "λ %x %y → %x";
        let result = parse_hsyntax(input);

        assert!(result.is_ok(), "Failed to parse hlambda: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: λ %x → λ %y → %x
        // %x is at index 1 in the innermost scope
        let expected = HSyntax::hlambda_rc(HSyntax::hlambda_rc(HSyntax::hvariable_rc(Index(1))));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hlambda_with_parens() {
        // Test parsing: (λ %x → %x)
        let input = "(λ %x → %x)";
        let result = parse_hsyntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse hlambda with parens: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: λ %x → %x
        let expected = HSyntax::hlambda_rc(HSyntax::hvariable_rc(Index(0)));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_happlication_simple() {
        // Test parsing: λ %f %x → %f %x
        // We need variables to be bound, so we use a lambda expression
        let input = "λ %f %x → %f %x";
        let result = parse_hsyntax(input);

        assert!(result.is_ok(), "Failed to parse happlication: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: λ %f → λ %x → %f %x
        // %f is at index 1 (skip over %x), %x is at index 0
        let expected = HSyntax::hlambda_rc(HSyntax::hlambda_rc(HSyntax::happlication_rc(
            HSyntax::hvariable_rc(Index(1)),
            HSyntax::hvariable_rc(Index(0)),
        )));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_happlication_left_associative() {
        // Test parsing: λ %f %x %y → %f %x %y
        // This should parse as: λ %f → λ %x → λ %y → ((%f %x) %y)
        // Application is left-associative
        let input = "λ %f %x %y → %f %x %y";
        let result = parse_hsyntax(input);

        assert!(result.is_ok(), "Failed to parse happlication: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: λ %f → λ %x → λ %y → ((%f %x) %y)
        // %f is at index 2, %x is at index 1, %y is at index 0
        let expected = HSyntax::hlambda_rc(HSyntax::hlambda_rc(HSyntax::hlambda_rc(
            HSyntax::happlication_rc(
                HSyntax::happlication_rc(
                    HSyntax::hvariable_rc(Index(2)),
                    HSyntax::hvariable_rc(Index(1)),
                ),
                HSyntax::hvariable_rc(Index(0)),
            ),
        )));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_happlication_constants() {
        // Test parsing: @42 @99
        let input = "@42 @99";
        let result = parse_hsyntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse happlication with constants: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: @42 @99
        use crate::syn::ConstantId;
        let expected = HSyntax::happlication_rc(
            HSyntax::hconstant_rc(ConstantId(42)),
            HSyntax::hconstant_rc(ConstantId(99)),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hcheck_simple() {
        // Test parsing: (λ %x → %x) : @42
        // We need a complete hterm to check, so we use a lambda
        let input = "(λ %x → %x) : @42";
        let result = parse_hsyntax(input);

        assert!(result.is_ok(), "Failed to parse hcheck: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: (λ %x → %x) : @42
        use crate::syn::ConstantId;
        let expected = HSyntax::hcheck_rc(
            HSyntax::hconstant_rc(ConstantId(42)),
            HSyntax::hlambda_rc(HSyntax::hvariable_rc(Index(0))),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hcheck_with_application() {
        // Test parsing: (@42 @99) : @100
        let input = "(@42 @99) : @100";
        let result = parse_hsyntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse hcheck with application: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: (@42 @99) : @100
        use crate::syn::ConstantId;
        let expected = HSyntax::hcheck_rc(
            HSyntax::hconstant_rc(ConstantId(100)),
            HSyntax::happlication_rc(
                HSyntax::hconstant_rc(ConstantId(42)),
                HSyntax::hconstant_rc(ConstantId(99)),
            ),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_splice_simple() {
        // Test parsing: ~@42
        let input = "~@42";
        let result = parse_hsyntax(input);

        assert!(result.is_ok(), "Failed to parse splice: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: ~@42
        use crate::syn::ConstantId;
        let expected = HSyntax::splice_rc(Syntax::constant_rc(ConstantId(42)));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_splice_with_lambda() {
        // Test parsing: ~(λ %x → %x)
        let input = "~(λ %x → %x)";
        let result = parse_hsyntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse splice with lambda: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: ~(λ %x → %x)
        let expected = HSyntax::splice_rc(Syntax::lambda_rc(Syntax::variable_rc(Index(0))));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_splice_with_universe() {
        // Test parsing: ~𝒰0
        let input = "~𝒰0";
        let result = parse_hsyntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse splice with universe: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: ~𝒰0
        let expected = HSyntax::splice_rc(Syntax::universe_rc(UniverseLevel::new(0)));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hterm_complex_nested() {
        // Test parsing: λ %f → (λ %x → %f %x) @42
        // This applies an inner lambda to a constant
        let input = "λ %f → (λ %x → %f %x) @42";
        let result = parse_hsyntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse complex nested hterm: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: λ %f → (λ %x → %f %x) @42
        use crate::syn::ConstantId;
        let expected = HSyntax::hlambda_rc(HSyntax::happlication_rc(
            HSyntax::hlambda_rc(HSyntax::happlication_rc(
                HSyntax::hvariable_rc(Index(1)), // %f
                HSyntax::hvariable_rc(Index(0)), // %x
            )),
            HSyntax::hconstant_rc(ConstantId(42)),
        ));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hterm_mixed_bound_unbound() {
        // Test parsing: λ %x %y → %y !0
        // %y is bound (index 0), !0 is unbound (index 2 at depth 2)
        let input = "λ %x %y → %y !0";
        let result = parse_hsyntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse mixed bound and unbound hterm: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: λ %x → λ %y → %y !0
        // %y has index 0, !0 has index 2
        let expected = HSyntax::hlambda_rc(HSyntax::hlambda_rc(HSyntax::happlication_rc(
            HSyntax::hvariable_rc(Index(0)),
            HSyntax::hvariable_rc(Index(2)),
        )));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hterm_splice_in_application() {
        // Test parsing: @42 ~𝒰0
        let input = "@42 ~𝒰0";
        let result = parse_hsyntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse splice in application: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: @42 ~𝒰0
        use crate::syn::ConstantId;
        let expected = HSyntax::happlication_rc(
            HSyntax::hconstant_rc(ConstantId(42)),
            HSyntax::splice_rc(Syntax::universe_rc(UniverseLevel::new(0))),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hterm_check_with_splice() {
        // Test parsing: ~@42 : @99
        let input = "~@42 : @99";
        let result = parse_hsyntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse check with splice: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: ~@42 : @99
        use crate::syn::ConstantId;
        let expected = HSyntax::hcheck_rc(
            HSyntax::hconstant_rc(ConstantId(99)),
            HSyntax::splice_rc(Syntax::constant_rc(ConstantId(42))),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hterm_unbound_variables_multiple() {
        // Test parsing: !0 !1 !2
        let input = "!0 !1 !2";
        let result = parse_hsyntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse multiple unbound variables: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: (!0 !1) !2
        // Application is left-associative
        let expected = HSyntax::happlication_rc(
            HSyntax::happlication_rc(
                HSyntax::hvariable_rc(Index(0)),
                HSyntax::hvariable_rc(Index(1)),
            ),
            HSyntax::hvariable_rc(Index(2)),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hterm_parentheses_precedence() {
        // Test parsing: @42 (@99 @100)
        // Should parse as: @42 (@99 @100), not (@42 @99) @100
        let input = "@42 (@99 @100)";
        let result = parse_hsyntax(input);

        assert!(
            result.is_ok(),
            "Failed to parse parentheses precedence: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: @42 (@99 @100)
        use crate::syn::ConstantId;
        let expected = HSyntax::happlication_rc(
            HSyntax::hconstant_rc(ConstantId(42)),
            HSyntax::happlication_rc(
                HSyntax::hconstant_rc(ConstantId(99)),
                HSyntax::hconstant_rc(ConstantId(100)),
            ),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hterm_roundtrip_examples() {
        use hwml_support::pp::dump_to_str;

        // Test that parsing and printing hterms works correctly
        let test_cases = vec![
            "@42",
            "!0",
            "λ %x → %x",
            "λ %x %y → %x",
            "@42 @99",
            "(λ %x → %x) : @42",
            "~@42",
            "λ %x → !0",
            "!0 !1",
        ];

        for input in test_cases {
            let parsed = parse_hsyntax(input).expect(&format!("Failed to parse: {}", input));

            // Also verify that the printed form can be understood
            let printed = dump_to_str(&parsed);

            // The printed form should be parseable
            let reparsed = parse_hsyntax(&printed);
            assert!(
                reparsed.is_ok(),
                "Failed to reparse printed form of '{}': printed='{}', error={:?}",
                input,
                printed,
                reparsed.err()
            );

            // The reparsed should equal the original
            assert_eq!(
                *reparsed.unwrap(),
                *parsed,
                "Round-trip failed for input: {} (printed: {})",
                input,
                printed
            );
        }
    }
}
