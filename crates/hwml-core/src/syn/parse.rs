use crate::common::{DBParseError, Index, Location, NegativeLevel};
use crate::declaration::{Declaration, Module};
use crate::syn::{CaseBranch, Closure, RcSyntax, Syntax, Telescope};
use crate::{declaration, ConstantId, MetaVariableId};
use core::fmt::Debug;
use hwml_support::FromWithDb;
use logos::{Lexer, Logos};
use salsa::Database;
use std::collections::HashMap;
use std::fmt;
use std::num::ParseIntError;
use std::ops::Range;

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub enum Error {
    InvalidToken(Range<usize>),
    InvalidInteger(String),
    MissingRParen,
    MissingRBracket,
    MissingLBracket,
    MissingArrow,
    MissingVariable,
    MissingTerm,
    MissingConstant,
    MissingPrimitive,
    MissingCaseBranch,
    MissingMetavariableId,
    UnknownVariable(String),
    DBParseError(DBParseError),
    MissingColon,
    MissingSemicolon,
    MissingDeclarationName,
    MissingDeclarationType,
    MissingDeclarationValue,
    MissingWhere,
    CaseScrutineeMustBeVariable,
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

#[derive(Logos, Clone, Debug, Eq, PartialEq, Hash)]
#[logos(error(Error, Error::from_lexer))]
// Whitespace
#[logos(skip r"\p{Whitespace}+")]
// Comments
#[logos(skip r"//[^\r\n]*")]
// Ids
#[logos(subpattern id = r"[^\p{gc=Separator}\p{gc=Control}():;,\[\]!\?\%<>]+")]
pub enum Token {
    #[token("∀", priority = 4)]
    #[token("forall", priority = 4)]
    Pi,
    #[token("λ", priority = 4)]
    #[token("\\", priority = 4)]
    Lambda,
    #[token("let", priority = 5)]
    Let,
    #[token("mod", priority = 5)]
    Mod,
    #[token("^", priority = 4)]
    Lift,
    #[token("^s", priority = 5)]
    SLift,
    #[token("^m", priority = 5)]
    MLift,
    #[token("(", priority = 10)]
    LParen,
    #[token(")", priority = 10)]
    RParen,
    #[token("[", priority = 10)]
    LBracket,
    #[token("]", priority = 10)]
    RBracket,
    #[token("<", priority = 10)]
    LAngle,
    #[token(">", priority = 10)]
    RAngle,
    #[token("→", priority = 5)]
    #[token("->", priority = 5)]
    Arrow,
    #[token("|-", priority = 6)]
    #[token("⊢", priority = 6)]
    Turnstile,
    #[token(":", priority = 4)]
    Colon,
    #[token("=", priority = 4)]
    Equals,
    #[token(",", priority = 10)]
    Comma,
    #[token("|", priority = 10)]
    Pipe,
    #[regex(r"U[0-9]+", priority = 4, callback = |lex| lex.slice()["U".len()..].parse())]
    #[regex(r"𝒰[0-9]+", priority = 4, callback = |lex| lex.slice()["𝒰".len()..].parse())]
    Universe(usize),
    #[token("HardwareUniverse", priority = 5)]
    HardwareUniverse,
    #[token("SignalUniverse", priority = 5)]
    SignalUniverse,
    #[token("ModuleUniverse", priority = 5)]
    ModuleUniverse,
    #[regex(r"@(?&id)+", priority = 4, callback = |lex| lex.slice()["@".len()..].to_owned())]
    Constant(String),
    #[regex(r"%(?&id)+", priority = 4, callback = |lex| lex.slice()["%".len()..].to_owned())]
    Variable(String),
    #[regex(r"![0-9]+", priority = 4, callback = |lex| lex.slice().parse())]
    UnboundVariable(NegativeLevel),
    #[regex(r"[0-9]+", priority = 3, callback = |lex| lex.slice().parse())]
    Number(usize),
    #[regex(r"\$(?&id)+", priority = 4, callback = |lex| lex.slice()["$".len()..].to_owned())]
    Primitive(String),
    #[token("Bit", priority = 6)]
    Bit,
    #[token("0", priority = 5)]
    Zero,
    #[token("1", priority = 5)]
    One,
    #[token("case", priority = 5)]
    Case,
    #[token("Eq", priority = 5)]
    Eq,
    #[token("refl", priority = 5)]
    Refl,
    #[token("transport", priority = 5)]
    Transport,
    #[token("{", priority = 10)]
    LBrace,
    #[token("}", priority = 10)]
    RBrace,
    #[token(";", priority = 10)]
    Semicolon,
    #[token("#[", priority = 10)]
    LHashBracket,
    #[token("?[", priority = 10)]
    LQuestionBracket,
    #[token("=>", priority = 5)]
    FatArrow,
    #[token("prim", priority = 5)]
    Prim,
    #[token("const", priority = 5)]
    Const,
    #[token("tcon", priority = 5)]
    TCon,
    #[token("dcon", priority = 5)]
    DCon,
    #[token("meta", priority = 5)]
    Meta,
    #[token("where", priority = 5)]
    Where,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

struct State<'input> {
    /// The database reference.
    db: &'input dyn Database,
    /// The names in scope. Each new name is pushed on the end.
    names: Vec<String>,
    /// Map from metavariable names to their IDs.
    meta_names: HashMap<String, MetaVariableId>,
    /// Counter for allocating new metavariable IDs.
    next_meta_id: usize,
    /// Counter for allocating new location IDs.
    next_location_id: u32,
    /// The main lexer.
    lexer: Lexer<'input, Token>,
    /// The current token. We support single token peeking.
    token: Option<ParseResult<Token>>,
}

impl<'input> State<'input> {
    fn new(db: &'input dyn Database, input: &'input str) -> State<'input> {
        let mut lexer = Token::lexer(input);
        let token = lexer.next();
        State {
            db,
            names: Vec::new(),
            meta_names: HashMap::new(),
            next_meta_id: 0,
            next_location_id: 1, // Start at 1, since 0 is UNKNOWN
            lexer,
            token,
        }
    }

    /// Get the database reference.
    fn db(&self) -> &'input dyn Database {
        self.db
    }

    /// Peek at the current token.
    fn peek_token(&self) -> Option<ParseResult<Token>> {
        self.token.clone()
    }

    /// Advance to the next token.
    fn advance_token(&mut self) {
        self.token = self.lexer.next();
    }

    /// Get the current span from the lexer.
    fn span(&self) -> Range<usize> {
        self.lexer.span()
    }

    /// Allocate a new Location from the current lexer span.
    fn alloc_location(&mut self) -> Location {
        let id = self.next_location_id;
        self.next_location_id += 1;
        Location(id)
    }

    /// Push a binder to the environment.
    fn push_name(&mut self, name: String) {
        self.names.push(name);
    }

    #[allow(dead_code)]
    fn extend_names<T>(&mut self, names: T)
    where
        T: IntoIterator<Item = String>,
    {
        for name in names {
            self.push_name(name);
        }
    }

    fn find_name(&self, name: &String) -> Option<Index> {
        self.names.iter().rev().enumerate().find_map(|(i, n)| {
            if name == n.as_str() {
                Some(Index::new(i))
            } else {
                None
            }
        })
    }

    /// Get the current depth of the name environment.
    fn names_depth(&self) -> usize {
        self.names.len()
    }

    /// Reset the name environment to a given depth.
    fn reset_names(&mut self, depth: usize) {
        self.names.truncate(depth);
    }

    /// Parse with additional variables in scope.
    #[allow(dead_code)]
    fn under_binders<T, F, R>(&mut self, names: T, block: F) -> R
    where
        T: IntoIterator<Item = String>,
        F: FnOnce(&mut Self) -> R,
    {
        let depth = self.names_depth();
        self.extend_names(names);
        let r = block(self);
        self.reset_names(depth);
        r
    }

    /// Get or create a metavariable ID for the given name. If the name already
    /// exists in the map, return the existing ID. Otherwise, allocate a new ID
    /// and store the mapping.
    fn get_or_create_meta_id(&mut self, name: String) -> MetaVariableId {
        if let Some(&id) = self.meta_names.get(&name) {
            // Name exists, return existing ID
            id
        } else {
            // Name doesn't exist, allocate new ID
            let id = MetaVariableId(self.next_meta_id);
            self.next_meta_id += 1;
            self.meta_names.insert(name, id);
            id
        }
    }
}

#[allow(dead_code)]
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

#[allow(dead_code)]
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

#[allow(dead_code)]
fn p_lbracket_opt(state: &mut State) -> ParseResult<Option<()>> {
    p_token_opt(state, Token::LBracket)
}

fn p_lbracket(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::LBracket, Error::MissingLBracket)
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

#[allow(dead_code)]
fn p_pipe(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::Pipe, Error::Other)
}

fn p_pipe_opt(state: &mut State) -> ParseResult<Option<()>> {
    p_token_opt(state, Token::Pipe)
}

fn p_colon(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::Colon, Error::Other)
}

fn p_colon_opt(state: &mut State) -> ParseResult<Option<()>> {
    p_token_opt(state, Token::Colon)
}

#[allow(dead_code)]
fn p_semicolon(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::Semicolon, Error::Other)
}

fn p_lparen(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::LParen, Error::Other)
}

fn p_lbrace(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::LBrace, Error::Other)
}

fn p_rbrace(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::RBrace, Error::Other)
}

#[allow(dead_code)]
fn p_semicolon_opt(state: &mut State) -> ParseResult<Option<()>> {
    p_token_opt(state, Token::Semicolon)
}

fn p_langle_opt(state: &mut State) -> ParseResult<Option<()>> {
    p_token_opt(state, Token::LAngle)
}

fn p_rangle(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::RAngle, Error::Other)
}

fn p_fat_arrow(state: &mut State) -> ParseResult<()> {
    p_token(state, Token::FatArrow, Error::Other)
}

fn p_constant_opt<'db>(state: &mut State<'db>) -> ParseResult<Option<ConstantId<'db>>> {
    match state.peek_token() {
        Some(Err(err)) => Err(err),
        Some(Ok(Token::Constant(name))) => {
            state.advance_token();
            Ok(Some(ConstantId::from_with_db(state.db(), &name)))
        }
        _ => Ok(None),
    }
}

fn p_constant<'db>(state: &mut State<'db>) -> ParseResult<ConstantId<'db>> {
    match p_constant_opt(state) {
        Err(e) => Err(e),
        Ok(Some(n)) => Ok(n),
        Ok(None) => Err(Error::MissingConstant),
    }
}

fn p_primitive_opt<'db>(state: &mut State<'db>) -> ParseResult<Option<ConstantId<'db>>> {
    match state.peek_token() {
        Some(Err(err)) => Err(err),
        Some(Ok(Token::Primitive(name))) => {
            state.advance_token();
            Ok(Some(ConstantId::from_with_db(state.db(), &name)))
        }
        _ => Ok(None),
    }
}

fn p_primitive<'db>(state: &mut State<'db>) -> ParseResult<ConstantId<'db>> {
    match p_primitive_opt(state) {
        Err(e) => Err(e),
        Ok(Some(n)) => Ok(n),
        Ok(None) => Err(Error::MissingPrimitive),
    }
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

fn p_metavariable_id(state: &mut State) -> ParseResult<MetaVariableId> {
    match state.peek_token() {
        Some(Ok(Token::Number(n))) => {
            // Numeric ID: ?[0], ?[1], etc.
            state.advance_token();
            Ok(MetaVariableId(n))
        }
        Some(Ok(Token::Zero)) => {
            state.advance_token();
            Ok(MetaVariableId(0))
        }
        Some(Ok(Token::One)) => {
            state.advance_token();
            Ok(MetaVariableId(1))
        }
        Some(Ok(Token::Variable(name))) => {
            // Named metavariable: ?[x], ?[myvar], etc.
            // Use get_or_create_meta_id to allocate or reuse an ID
            let name = name.clone();
            state.advance_token();
            Ok(state.get_or_create_meta_id(name))
        }
        _ => Err(Error::MissingMetavariableId),
    }
}

fn p_pi_binder_opt<'db>(state: &mut State<'db>) -> ParseResult<Option<RcSyntax<'db>>> {
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

/// Parse a telescope of binders: `(%x : T1) (%y : T2) ...`
/// Returns a vector of types, where each binder extends the name environment
/// so subsequent binders can reference earlier ones.
fn p_telescope<'db>(state: &mut State<'db>) -> ParseResult<Vec<RcSyntax<'db>>> {
    let mut types = Vec::new();
    loop {
        match p_pi_binder_opt(state) {
            Ok(Some(ty)) => types.push(ty),
            Ok(None) => break,
            Err(e) => return Err(e),
        }
    }
    Ok(types)
}

// Parse a transport motive: [%x %y ...] |- body
// This introduces binders and returns a Closure
fn p_transport_motive<'db>(state: &mut State<'db>) -> ParseResult<Closure<'db>> {
    p_lbracket(state)?;

    // Parse variable binders (e.g., %0, %x, %y, ...)
    let mut var_names = Vec::new();
    loop {
        match p_variable_opt(state)? {
            Some(name) => var_names.push(name),
            None => break,
        }
    }

    // Expect the closing bracket
    p_rbracket(state)?;

    // Expect the turnstile token |-
    p_token(state, Token::Turnstile, Error::MissingTerm)?;

    // Push all binder names onto the stack
    for name in &var_names {
        state.push_name(name.clone());
    }

    // Parse the body term
    let body = p_atom(state)?;

    // Pop all binders
    for _ in 0..var_names.len() {
        state.names.pop();
    }

    // Build nested closures from right to left, similar to how Lambda works
    // [%0 %1] |- body becomes Closure { body: Syntax::Closure(Closure { body: body }) }
    let mut result = body;
    for _ in 0..var_names.len() {
        result = Syntax::closure_rc(Location::UNKNOWN, result);
    }

    // The outermost wrapper is a Syntax::Closure, extract it
    match &*result {
        Syntax::Closure(c) => Ok(c.clone()),
        _ => unreachable!("We just built a closure"),
    }
}

// Parse an atomic term (no operators)
fn p_atom_opt<'db>(state: &mut State<'db>) -> ParseResult<Option<RcSyntax<'db>>> {
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
                let lambda_loc = state.alloc_location();
                state.advance_token();
                let depth = state.names_depth();
                let mut i = 0;
                loop {
                    match p_variable_opt(state) {
                        Err(e) => return Err(e),
                        Ok(Some(var)) => {
                            i = i + 1;
                            // Introduce binders into the unified environment
                            state.push_name(var)
                        }
                        Ok(None) => break,
                    }
                }
                p_arrow(state)?;
                let body = p_harrow(state)?;
                state.reset_names(depth);
                // Build nested lambdas from right to left
                // For now, all nested lambdas share the same location (the λ token)
                let mut result = body;
                for _ in 0..i {
                    result = Syntax::lambda_rc_with_loc(lambda_loc, result);
                }
                Ok(Some(result))
            }
            Token::Let => {
                // Parse: let %x : T = v; body
                let loc = state.alloc_location();
                state.advance_token();
                let depth = state.names_depth();

                // Parse the variable name
                let var_name = match state.peek_token() {
                    Some(Ok(Token::Variable(name))) => {
                        state.advance_token();
                        name
                    }
                    _ => return Err(Error::MissingVariable),
                };

                // Expect ':'
                p_token(state, Token::Colon, Error::MissingColon)?;

                // Parse the type annotation
                let ty = p_term(state)?;

                // Expect '='
                p_token(state, Token::Equals, Error::Other)?;

                // Parse the value
                let value = p_term(state)?;

                // Expect ';'
                p_token(state, Token::Semicolon, Error::MissingSemicolon)?;

                // Push the variable name into scope for the body
                state.push_name(var_name);

                // Parse the body
                let body = p_term(state)?;

                // Restore the name environment
                state.reset_names(depth);

                Ok(Some(Syntax::let_rc_with_loc(loc, ty, value, body)))
            }
            Token::Mod => {
                let mod_loc = state.alloc_location();
                state.advance_token();
                let depth = state.names_depth();
                let mut i = 0;
                loop {
                    match p_variable_opt(state) {
                        Err(e) => return Err(e),
                        Ok(Some(var)) => {
                            i = i + 1;
                            // Introduce binders into the unified environment
                            state.push_name(var)
                        }
                        Ok(None) => break,
                    }
                }
                p_arrow(state)?;
                let body = p_harrow(state)?;
                state.reset_names(depth);
                // Build nested modules from right to left
                let mut result = body;
                for _ in 0..i {
                    result = Syntax::module_rc_with_loc(mod_loc, result);
                }
                Ok(Some(result))
            }
            Token::Pi => {
                let pi_loc = state.alloc_location();
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
                    result = Syntax::pi_rc_with_loc(pi_loc, ty.clone(), result);
                }
                Ok(Some(result))
            }
            Token::LBracket => {
                let loc = state.alloc_location();
                state.advance_token();
                let constructor = p_constant(state)?;
                let mut arguments = Vec::new();
                loop {
                    match p_atom_opt(state) {
                        Err(e) => return Err(e),
                        Ok(Some(term)) => arguments.push(term),
                        Ok(None) => break,
                    }
                }
                p_rbracket(state)?;
                Ok(Some(Syntax::data_constructor_rc_with_loc(
                    loc,
                    constructor,
                    arguments,
                )))
            }
            Token::LHashBracket => {
                let loc = state.alloc_location();
                state.advance_token();
                let constructor = p_constant(state)?;
                let mut arguments = Vec::new();
                loop {
                    match p_atom_opt(state) {
                        Err(e) => return Err(e),
                        Ok(Some(term)) => arguments.push(term),
                        Ok(None) => break,
                    }
                }
                p_rbracket(state)?;
                Ok(Some(Syntax::type_constructor_rc_with_loc(
                    loc,
                    constructor,
                    arguments,
                )))
            }
            Token::Variable(name) => {
                let loc = state.alloc_location();
                state.advance_token();
                // Look it up in the unified environment
                match state.find_name(&name) {
                    Some(index) => Ok(Some(Syntax::variable_rc_with_loc(loc, index))),
                    _ => Err(Error::UnknownVariable(name)),
                }
            }
            Token::UnboundVariable(negative_level) => {
                let loc = state.alloc_location();
                state.advance_token();
                // Convert negative level to index using the current depth:
                // index = depth + negative_level
                let index = negative_level.to_index(state.names_depth());
                Ok(Some(Syntax::variable_rc_with_loc(loc, index)))
            }
            Token::Universe(level) => {
                let loc = state.alloc_location();
                state.advance_token();
                Ok(Some(Syntax::universe_rc_with_loc(
                    loc,
                    crate::common::UniverseLevel::new(level),
                )))
            }
            Token::HardwareUniverse => {
                let loc = state.alloc_location();
                state.advance_token();
                Ok(Some(Syntax::hardware_rc_with_loc(loc)))
            }
            Token::Constant(name) => {
                let loc = state.alloc_location();
                state.advance_token();
                Ok(Some(Syntax::constant_rc_with_loc_from(
                    loc,
                    state.db(),
                    &name,
                )))
            }
            Token::LQuestionBracket => {
                let loc = state.alloc_location();
                state.advance_token();
                // Expect ?[id term1 term2 ...] or ?[name term1 term2 ...]
                let id = p_metavariable_id(state)?;
                // Parse space-separated substitution terms (atomic terms only)
                let mut substitution = Vec::new();
                loop {
                    match p_atom_opt(state) {
                        Ok(Some(term)) => substitution.push(term),
                        Ok(None) => break,
                        Err(err) => return Err(err),
                    }
                }
                p_rbracket(state)?;
                Ok(Some(Syntax::metavariable_rc_with_loc(
                    loc,
                    id,
                    substitution,
                )))
            }
            Token::Lift => {
                let loc = state.alloc_location();
                state.advance_token();
                let tm = p_atom(state)?;
                Ok(Some(Syntax::lift_rc_with_loc(loc, tm)))
            }
            Token::SLift => {
                let loc = state.alloc_location();
                state.advance_token();
                let tm = p_atom(state)?;
                Ok(Some(Syntax::slift_rc_with_loc(loc, tm)))
            }
            Token::MLift => {
                let loc = state.alloc_location();
                state.advance_token();
                let tm = p_atom(state)?;
                Ok(Some(Syntax::mlift_rc_with_loc(loc, tm)))
            }
            Token::SignalUniverse => {
                let loc = state.alloc_location();
                state.advance_token();
                Ok(Some(Syntax::signal_universe_rc_with_loc(loc)))
            }
            Token::ModuleUniverse => {
                let loc = state.alloc_location();
                state.advance_token();
                Ok(Some(Syntax::module_universe_rc_with_loc(loc)))
            }
            Token::Bit => {
                let loc = state.alloc_location();
                state.advance_token();
                Ok(Some(Syntax::bit_rc_with_loc(loc)))
            }
            Token::Zero => {
                let loc = state.alloc_location();
                state.advance_token();
                Ok(Some(Syntax::zero_rc_with_loc(loc)))
            }
            Token::One => {
                let loc = state.alloc_location();
                state.advance_token();
                Ok(Some(Syntax::one_rc_with_loc(loc)))
            }
            Token::Eq => {
                // Parse: Eq A x y
                let loc = state.alloc_location();
                state.advance_token();
                let ty = p_atom(state)?;
                let lhs = p_atom(state)?;
                let rhs = p_atom(state)?;
                Ok(Some(Syntax::eq_rc_with_loc(loc, ty, lhs, rhs)))
            }
            Token::Refl => {
                // Parse: refl
                let loc = state.alloc_location();
                state.advance_token();
                Ok(Some(Syntax::refl_rc_with_loc(loc)))
            }
            Token::Transport => {
                // Parse: transport [%x -> body] proof value
                let loc = state.alloc_location();
                state.advance_token();

                // Parse the motive closure: [%x -> body]
                let motive = p_transport_motive(state)?;

                // Parse proof and value
                let proof = p_atom(state)?;
                let value = p_atom(state)?;

                Ok(Some(Syntax::transport_rc_with_loc(
                    loc, motive, proof, value,
                )))
            }
            Token::Primitive(name) => {
                let loc = state.alloc_location();
                state.advance_token();
                Ok(Some(Syntax::prim_rc_with_loc_from(loc, state.db(), &name)))
            }
            _ => Ok(None),
        },
        None => Ok(None),
    }
}

fn p_atom<'db>(state: &mut State<'db>) -> ParseResult<RcSyntax<'db>> {
    match p_atom_opt(state) {
        Err(err) => Err(err),
        Ok(None) => Err(Error::MissingTerm),
        Ok(Some(term)) => Ok(term),
    }
}

/// @Foo %0 %1
fn p_case_pattern_opt<'db>(
    state: &mut State<'db>,
) -> ParseResult<Option<(ConstantId<'db>, usize)>> {
    let Some(constructor) = p_constant_opt(state)? else {
        return Ok(None);
    };
    let mut arity = 0;
    while let Some(name) = p_variable_opt(state)? {
        arity += 1;
        state.push_name(name)
    }
    Ok(Some((constructor, arity)))
}

/// @Foo %0 %1 => body;
fn p_case_branch_opt<'db>(state: &mut State<'db>) -> ParseResult<Option<CaseBranch<'db>>> {
    // Save the current depth so we can restore the environment
    // after parsing this branch. The branch pattern introduces
    // new binders (one per argument), which are in scope for the
    // branch body but must be popped afterwards.
    let depth = state.names_depth();
    let Some((constructor, arity)) = p_case_pattern_opt(state)? else {
        return Ok(None);
    };
    p_fat_arrow(state)?;
    let body = p_term(state)?;
    state.reset_names(depth);
    Ok(Some(CaseBranch::new(constructor, arity, body)))
}

fn p_case_branch<'db>(state: &mut State<'db>) -> ParseResult<CaseBranch<'db>> {
    match p_case_branch_opt(state) {
        Err(err) => Err(err),
        Ok(None) => Err(Error::MissingCaseBranch),
        Ok(Some(term)) => Ok(term),
    }
}

fn p_case_branches<'db>(state: &mut State<'db>) -> ParseResult<Vec<CaseBranch<'db>>> {
    p_lbrace(state)?;
    let mut branches = Vec::new();

    if let Some(branch) = p_case_branch_opt(state)? {
        branches.push(branch);
    }

    while let Some(()) = p_pipe_opt(state)? {
        branches.push(p_case_branch(state)?);
    }

    p_rbrace(state)?;
    Ok(branches)
}

fn p_trailing_case_opt<'db>(
    state: &mut State<'db>,
    lead: &RcSyntax<'db>,
) -> ParseResult<Option<RcSyntax<'db>>> {
    if p_token_opt(state, Token::Case)?.is_none() {
        return Ok(None);
    }
    let loc = state.alloc_location();
    // The scrutinee must be a variable (not an arbitrary expression).
    // This constraint is essential for dependent pattern matching - the pattern
    // unifier needs to know exactly which variable it's solving for.
    // Extract the Index from the lead expression.
    use crate::syn::SyntaxData;
    let scrutinee_index = match &lead.data {
        SyntaxData::Variable(var) => var.index,
        _ => return Err(Error::CaseScrutineeMustBeVariable),
    };
    let branches = p_case_branches(state)?;
    Ok(Some(Syntax::case_rc_with_loc(
        loc,
        scrutinee_index,
        branches,
    )))
}

// Parse application with bracket notation: f[x, y, z]
fn p_trailing_app_opt<'db>(
    state: &mut State<'db>,
    lead: &RcSyntax<'db>,
) -> ParseResult<Option<RcSyntax<'db>>> {
    // Check for opening bracket
    if p_token_opt(state, Token::LBracket)?.is_none() {
        return Ok(None);
    }

    // Parse comma-separated arguments
    let mut args = Vec::new();

    // Parse first argument (optional - allows f[] syntax)
    if let Some(arg) = p_term_opt(state)? {
        args.push(arg);

        // Parse remaining arguments after commas
        while p_token_opt(state, Token::Comma)?.is_some() {
            args.push(p_term(state)?);
        }
    }

    // Expect closing bracket
    p_rbracket(state)?;

    // Build nested applications from left to right: f[x, y, z] => ((f x) y) z
    let mut result = lead.clone();
    for arg in args {
        let app_loc = state.alloc_location();
        result = Syntax::application_rc_with_loc(app_loc, result, arg);
    }

    Ok(Some(result))
}

// Parse happlication with angle bracket type notation: f<T>(x)
fn p_trailing_happ_opt<'db>(
    state: &mut State<'db>,
    lead: &RcSyntax<'db>,
) -> ParseResult<Option<RcSyntax<'db>>> {
    // Check for opening angle bracket for type
    if p_langle_opt(state)?.is_none() {
        return Ok(None);
    }

    // Parse the module type
    let module_ty = p_term(state)?;

    // Expect closing angle bracket
    p_rangle(state)?;

    // Expect opening parenthesis for argument
    p_lparen(state)?;

    // Parse the argument
    let argument = p_term(state)?;

    // Expect closing parenthesis
    p_rparen(state)?;

    // Build happlication: module<module_ty>(argument)
    Ok(Some(Syntax::happlication_rc(
        Location::UNKNOWN,
        lead.clone(),
        module_ty,
        argument,
    )))
}

/// Parse a trailing eliminator.
fn p_trailing_elim_opt<'db>(
    state: &mut State<'db>,
    lead: &RcSyntax<'db>,
) -> ParseResult<Option<RcSyntax<'db>>> {
    match p_trailing_case_opt(state, lead)? {
        Some(term) => return Ok(Some(term)),
        None => (),
    }
    match p_trailing_app_opt(state, lead)? {
        Some(term) => return Ok(Some(term)),
        None => (),
    }
    match p_trailing_happ_opt(state, lead)? {
        Some(term) => return Ok(Some(term)),
        None => (),
    }
    // Juxtaposition-based application: f x (space-separated)
    // Try to parse another atom - if successful, it's an application
    match p_atom_opt(state)? {
        Some(arg) => {
            let app_loc = state.alloc_location();
            return Ok(Some(Syntax::application_rc_with_loc(
                app_loc,
                lead.clone(),
                arg,
            )));
        }
        None => (),
    }
    Ok(None)
}

/// Parse any eliminated term.
fn p_elim_opt<'db>(state: &mut State<'db>) -> ParseResult<Option<RcSyntax<'db>>> {
    // Leading subexpression.
    let mut term = match p_atom_opt(state) {
        Ok(Some(x)) => x,
        Ok(None) => return Ok(None),
        Err(e) => return Err(e),
    };

    // Trailing eliminators.
    loop {
        term = match p_trailing_elim_opt(state, &term) {
            Ok(Some(x)) => x,
            Ok(None) => return Ok(Some(term)),
            Err(e) => return Err(e),
        }
    }
}

fn p_harrow_opt<'db>(state: &mut State<'db>) -> ParseResult<Option<RcSyntax<'db>>> {
    let Some(term) = p_elim_opt(state)? else {
        return Ok(None);
    };

    if let Some(()) = p_arrow_opt(state)? {
        Ok(Some(Syntax::harrow_rc(
            Location::UNKNOWN,
            term,
            p_harrow(state)?,
        )))
    } else {
        Ok(Some(term))
    }
}

fn p_harrow<'db>(state: &mut State<'db>) -> ParseResult<RcSyntax<'db>> {
    match p_harrow_opt(state) {
        Ok(None) => Err(Error::MissingTerm),
        Ok(Some(term)) => Ok(term),
        Err(err) => Err(err),
    }
}

// Parse check (type annotation): term : type
fn p_check_opt<'db>(state: &mut State<'db>) -> ParseResult<Option<RcSyntax<'db>>> {
    let Some(term) = p_harrow_opt(state)? else {
        return Ok(None);
    };

    // Check if there's a colon.
    if let Some(()) = p_colon_opt(state)? {
        let loc = state.alloc_location();
        Ok(Some(Syntax::check_rc_with_loc(loc, p_term(state)?, term)))
    } else {
        Ok(Some(term))
    }
}

fn p_term_opt<'db>(state: &mut State<'db>) -> ParseResult<Option<RcSyntax<'db>>> {
    p_check_opt(state)
}

fn p_term<'db>(state: &mut State<'db>) -> ParseResult<RcSyntax<'db>> {
    match p_term_opt(state) {
        Err(err) => Err(err),
        Ok(None) => Err(Error::MissingTerm),
        Ok(Some(term)) => Ok(term),
    }
}

pub fn parse_syntax<'db>(db: &'db dyn Database, input: &'db str) -> ParseResult<RcSyntax<'db>> {
    let mut state = State::new(db, input);
    p_term(&mut state)
}

/// Parse syntax with a specific depth context.
/// This allows referencing variables by index (e.g., %0, %1, etc.).
/// The `depth` parameter specifies how many variables are in scope.
/// Variables are given dummy names ("0", "1", etc.) for parsing.
pub fn parse_syntax_at_depth<'db>(
    db: &'db dyn Database,
    input: &'db str,
    depth: usize,
) -> ParseResult<RcSyntax<'db>> {
    let mut state = State::new(db, input);
    // Add dummy variable names to the parser state
    for i in 0..depth {
        state.push_name(format!("{}", i));
    }
    p_term(&mut state)
}

/// Parse a primitive declaration: prim $Name : Type;
fn p_prim_decl<'db>(state: &mut State<'db>) -> ParseResult<Declaration<'db>> {
    // Expect 'prim' token
    p_token(state, Token::Prim, Error::Other)?;

    // Parse the name (primitives use $Name syntax)
    let name = p_primitive(state)?;

    // Expect ':'
    p_token(state, Token::Colon, Error::MissingColon)?;

    // Parse the type
    let ty = p_term(state)?;

    // Expect ';'
    p_token(state, Token::Semicolon, Error::MissingSemicolon)?;

    Ok(Declaration::primitive(name, ty))
}

/// Parse a constant declaration: const Name : Type = Value;
fn p_const_decl<'db>(state: &mut State<'db>) -> ParseResult<Declaration<'db>> {
    // Expect 'const' token
    p_token(state, Token::Const, Error::Other)?;

    // Parse the name
    let name = p_constant(state)?;

    // Expect ':'
    p_token(state, Token::Colon, Error::MissingColon)?;

    // Parse the type
    let ty = p_term(state)?;

    // Check for optional '= value'
    let value = if let Some(Ok(Token::Equals)) = state.peek_token() {
        state.advance_token(); // consume '='
        p_term(state)?
    } else {
        // If no value is provided, use the type as a placeholder
        ty.clone()
    };

    // Expect ';'
    p_token(state, Token::Semicolon, Error::MissingSemicolon)?;

    Ok(Declaration::constant(name, ty, value))
}

/// Parse a data constructor: dcon Name (%param1 : Type1) ... : Type
/// Returns (name, parameters telescope, result type)
fn p_dcon<'db>(
    state: &mut State<'db>,
) -> ParseResult<(ConstantId<'db>, Telescope<'db>, RcSyntax<'db>)> {
    // Expect 'dcon' token
    p_token(state, Token::DCon, Error::Other)?;

    // Parse the name
    let name = p_constant(state)?;

    // Save the current depth to restore later
    let depth = state.names_depth();

    // Parse parameter binders: (%name : type)*
    let param_tys = match p_telescope(state) {
        Ok(tys) => tys,
        Err(e) => {
            state.reset_names(depth);
            return Err(e);
        }
    };

    // Expect ':'
    if let Err(e) = p_token(state, Token::Colon, Error::MissingColon) {
        state.reset_names(depth);
        return Err(e);
    }

    // Parse the result type (can reference parameters)
    let result_ty = match p_term(state) {
        Ok(ty) => ty,
        Err(e) => {
            state.reset_names(depth);
            return Err(e);
        }
    };

    // Reset the name environment
    state.reset_names(depth);

    // Convert Vec to Telescope
    let telescope = Telescope::new(param_tys);

    Ok((name, telescope, result_ty))
}

/// Parse a type constructor declaration with optional data constructors:
/// tcon Name (%param1 : Type1) (%param2 : Type2) : (%index1 : Type3) (%index2 : Type4) -> Universe where
///   dcon Constructor1 : Type
///   dcon Constructor2 : Type
/// ;
fn p_tcon_decl<'db>(state: &mut State<'db>) -> ParseResult<Vec<Declaration<'db>>> {
    // Expect 'tcon' token
    p_token(state, Token::TCon, Error::Other)?;

    // Parse the type constructor name
    let tcon_name = p_constant(state)?;

    // Save the current depth to restore later
    let depth = state.names_depth();

    // Parse parameter binders: (%name : type)*
    let param_tys = match p_telescope(state) {
        Ok(tys) => tys,
        Err(e) => {
            state.reset_names(depth);
            return Err(e);
        }
    };

    // Save the depth after parameters (this is what dcons should see)
    let depth_after_params = state.names_depth();

    // Expect ':'
    if let Err(e) = p_token(state, Token::Colon, Error::MissingColon) {
        state.reset_names(depth);
        return Err(e);
    }

    // Parse index binders: (%name : type)*
    let index_tys = match p_telescope(state) {
        Ok(tys) => tys,
        Err(e) => {
            state.reset_names(depth);
            return Err(e);
        }
    };

    // Expect '->'
    if let Err(e) = p_token(state, Token::Arrow, Error::Other) {
        state.reset_names(depth);
        return Err(e);
    }

    // Parse the universe (can reference parameters and indices)
    let universe = match p_term(state) {
        Ok(ty) => ty,
        Err(e) => {
            state.reset_names(depth);
            return Err(e);
        }
    };

    let mut data_constructors = Vec::new();

    // Check for optional 'where' clause with data constructors
    if p_token_opt(state, Token::Where)?.is_some() {
        // Parse data constructors until we hit a semicolon
        // Data constructors can reference the parameters (but not the indices)
        loop {
            // Reset to depth after parameters before parsing each dcon
            state.reset_names(depth_after_params);

            // Try to parse a data constructor
            if let Some(Ok(Token::DCon)) = state.peek_token() {
                let (dcon_name, dcon_params, dcon_result_ty) = match p_dcon(state) {
                    Ok(result) => result,
                    Err(e) => {
                        state.reset_names(depth);
                        return Err(e);
                    }
                };
                data_constructors.push(declaration::DataConstructor::new(
                    dcon_name,
                    dcon_params,
                    dcon_result_ty,
                ));
            } else {
                break;
            }
        }
    }

    // Reset the name environment
    state.reset_names(depth);

    // Expect ';'
    p_token(state, Token::Semicolon, Error::MissingSemicolon)?;

    // Create the type constructor declaration with its data constructors
    // Store just the universe, not the full Pi type
    let parameters = Telescope::new(param_tys);
    let indices = Telescope::new(index_tys);
    let tcon_decl =
        Declaration::type_constructor(tcon_name, parameters, indices, data_constructors, universe);

    Ok(vec![tcon_decl])
}

/// Parse a metavariable declaration: meta ?[id] (%x : T1) (%y : T2) : Type;
/// The arguments telescope is optional.
fn p_meta_decl<'db>(state: &mut State<'db>) -> ParseResult<Declaration<'db>> {
    // Expect 'meta' token
    p_token(state, Token::Meta, Error::Other)?;

    // Expect '?['
    p_token(state, Token::LQuestionBracket, Error::Other)?;

    // Parse the metavariable ID
    let id = p_metavariable_id(state)?;

    // Expect ']'
    p_token(state, Token::RBracket, Error::MissingRBracket)?;

    // Save the current depth to restore later
    let depth = state.names_depth();

    // Parse optional argument binders: (%x : T1) (%y : T2) ...
    let arguments = match p_telescope(state) {
        Ok(tys) => tys,
        Err(e) => {
            state.reset_names(depth);
            return Err(e);
        }
    };

    // Expect ':'
    p_token(state, Token::Colon, Error::MissingColon)?;

    // Parse the type
    let ty = p_term(state)?;

    // Reset the name environment
    state.reset_names(depth);

    // Expect ';'
    p_token(state, Token::Semicolon, Error::MissingSemicolon)?;

    Ok(Declaration::metavariable(id, arguments.into(), ty))
}

/// Parse a single declaration.
fn p_declaration<'db>(state: &mut State<'db>) -> ParseResult<Option<Vec<Declaration<'db>>>> {
    match state.peek_token() {
        Some(Ok(Token::Prim)) => Ok(Some(vec![p_prim_decl(state)?])),
        Some(Ok(Token::Const)) => Ok(Some(vec![p_const_decl(state)?])),
        Some(Ok(Token::TCon)) => Ok(Some(p_tcon_decl(state)?)),
        Some(Ok(Token::Meta)) => Ok(Some(vec![p_meta_decl(state)?])),
        Some(Err(err)) => Err(err.clone()),
        _ => Ok(None),
    }
}

/// Parse a module (list of declarations).
pub fn parse_module<'db>(db: &'db dyn Database, input: &'db str) -> ParseResult<Module<'db>> {
    let mut state = State::new(db, input);
    let mut all_declarations = Vec::new();

    // Parse declarations until we run out of input
    while let Some(decls) = p_declaration(&mut state)? {
        all_declarations.extend(decls);
    }

    Ok(Module::from_declarations(all_declarations))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{Index, MetaVariableId, UniverseLevel};
    use crate::syn::print::print_syntax_to_string;
    use crate::ConstantId;
    use crate::Database;

    /// Parse helper - panics with message on failure
    fn parse<'db>(db: &'db Database, input: &'db str) -> RcSyntax<'db> {
        parse_syntax(db, input).unwrap_or_else(|e| panic!("Failed to parse '{}': {:?}", input, e))
    }

    #[test]
    fn test_parse_lambda_single_var() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "λ %0 → %0"),
            Syntax::lambda_rc(
                Location::UNKNOWN,
                Syntax::variable_rc(Location::UNKNOWN, Index(0))
            )
        );
    }

    #[test]
    fn test_parse_lambda_multiple_vars() {
        let db = Database::new();
        // λ %x %y → %x  =>  λ → λ → %1 (nested lambdas, %x at index 1)
        assert_eq!(
            parse(&db, "λ %x %y → %x"),
            Syntax::lambda_rc(
                Location::UNKNOWN,
                Syntax::lambda_rc(
                    Location::UNKNOWN,
                    Syntax::variable_rc(Location::UNKNOWN, Index(1))
                )
            )
        );
    }

    #[test]
    fn test_parse_lambda_with_parens() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "(λ %0 → %0)"),
            Syntax::lambda_rc(
                Location::UNKNOWN,
                Syntax::variable_rc(Location::UNKNOWN, Index(0))
            )
        );
    }

    #[test]
    fn test_parse_pi_simple() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "∀(%x : 𝒰0) → 𝒰0"),
            Syntax::pi_rc(
                Location::UNKNOWN,
                Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)),
                Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0))
            )
        );
    }

    #[test]
    fn test_parse_universe() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "𝒰0"),
            Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0))
        );
    }

    #[test]
    fn test_parse_pi_multiple_vars() {
        let db = Database::new();
        // ∀(%x : 𝒰0) (%y : 𝒰0) → %x  =>  nested Pi, %x at index 1
        assert_eq!(
            parse(&db, "∀(%x : 𝒰0) (%y : 𝒰0) → %x"),
            Syntax::pi_rc(
                Location::UNKNOWN,
                Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)),
                Syntax::pi_rc(
                    Location::UNKNOWN,
                    Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)),
                    Syntax::variable_rc(Location::UNKNOWN, Index(1))
                )
            )
        );
    }

    #[test]
    fn test_parse_application_simple() {
        let db = Database::new();
        // λ %f %x → %f %x  =>  λ → λ → app(%1, %0)
        assert_eq!(
            parse(&db, "λ %f %x → %f %x"),
            Syntax::lambda_rc(
                Location::UNKNOWN,
                Syntax::lambda_rc(
                    Location::UNKNOWN,
                    Syntax::application_rc(
                        Location::UNKNOWN,
                        Syntax::variable_rc(Location::UNKNOWN, Index(1)),
                        Syntax::variable_rc(Location::UNKNOWN, Index(0))
                    )
                )
            )
        );
    }

    #[test]
    fn test_parse_application_left_associative() {
        let db = Database::new();
        // λ %f %x %y → %f %x %y  =>  λ → λ → λ → app(app(%2, %1), %0)
        assert_eq!(
            parse(&db, "λ %f %x %y → %f %x %y"),
            Syntax::lambda_rc(
                Location::UNKNOWN,
                Syntax::lambda_rc(
                    Location::UNKNOWN,
                    Syntax::lambda_rc(
                        Location::UNKNOWN,
                        Syntax::application_rc(
                            Location::UNKNOWN,
                            Syntax::application_rc(
                                Location::UNKNOWN,
                                Syntax::variable_rc(Location::UNKNOWN, Index(2)),
                                Syntax::variable_rc(Location::UNKNOWN, Index(1))
                            ),
                            Syntax::variable_rc(Location::UNKNOWN, Index(0))
                        )
                    )
                )
            )
        );
    }

    #[test]
    fn test_parse_check() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "(λ %x → %x) : 𝒰0"),
            Syntax::check_rc(
                Location::UNKNOWN,
                Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)),
                Syntax::lambda_rc(
                    Location::UNKNOWN,
                    Syntax::variable_rc(Location::UNKNOWN, Index(0))
                )
            )
        );
    }

    #[test]
    fn test_parse_check_with_application() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "(λ %f %x → %f %x) : 𝒰0"),
            Syntax::check_rc(
                Location::UNKNOWN,
                Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)),
                Syntax::lambda_rc(
                    Location::UNKNOWN,
                    Syntax::lambda_rc(
                        Location::UNKNOWN,
                        Syntax::application_rc(
                            Location::UNKNOWN,
                            Syntax::variable_rc(Location::UNKNOWN, Index(1)),
                            Syntax::variable_rc(Location::UNKNOWN, Index(0))
                        )
                    )
                )
            )
        );
    }

    #[test]
    fn test_parse_lambda_application() {
        let db = Database::new();
        // λ %x → (λ %y → %y) %x  =>  λ → app(λ → %0, %0)
        assert_eq!(
            parse(&db, "λ %x → (λ %y → %y) %x"),
            Syntax::lambda_rc(
                Location::UNKNOWN,
                Syntax::application_rc(
                    Location::UNKNOWN,
                    Syntax::lambda_rc(
                        Location::UNKNOWN,
                        Syntax::variable_rc(Location::UNKNOWN, Index(0))
                    ),
                    Syntax::variable_rc(Location::UNKNOWN, Index(0))
                )
            )
        );
    }

    #[test]
    fn test_parse_metavariable_simple() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "?[0]"),
            Syntax::metavariable_rc(Location::UNKNOWN, MetaVariableId(0), vec![])
        );
    }

    #[test]
    fn test_parse_metavariable_multiple() {
        let db = Database::new();
        // ?[0] ?[1] ?[0]  =>  app(app(?[0], ?[1]), ?[0])
        assert_eq!(
            parse(&db, "?[0] ?[1] ?[0]"),
            Syntax::application_rc(
                Location::UNKNOWN,
                Syntax::application_rc(
                    Location::UNKNOWN,
                    Syntax::metavariable_rc(Location::UNKNOWN, MetaVariableId(0), vec![]),
                    Syntax::metavariable_rc(Location::UNKNOWN, MetaVariableId(1), vec![])
                ),
                Syntax::metavariable_rc(Location::UNKNOWN, MetaVariableId(0), vec![])
            )
        );
    }

    #[test]
    fn test_parse_metavariable_in_lambda() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "λ %x → ?[0] %x"),
            Syntax::lambda_rc(
                Location::UNKNOWN,
                Syntax::application_rc(
                    Location::UNKNOWN,
                    Syntax::metavariable_rc(Location::UNKNOWN, MetaVariableId(0), vec![]),
                    Syntax::variable_rc(Location::UNKNOWN, Index(0))
                )
            )
        );
    }

    #[test]
    fn test_parse_metavariable_ordering() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "?[0] ?[1] ?[2]"),
            Syntax::application_rc(
                Location::UNKNOWN,
                Syntax::application_rc(
                    Location::UNKNOWN,
                    Syntax::metavariable_rc(Location::UNKNOWN, MetaVariableId(0), vec![]),
                    Syntax::metavariable_rc(Location::UNKNOWN, MetaVariableId(1), vec![])
                ),
                Syntax::metavariable_rc(Location::UNKNOWN, MetaVariableId(2), vec![])
            )
        );
    }

    #[test]
    fn test_parse_metavariable_with_type() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "?[0] : 𝒰0"),
            Syntax::check_rc(
                Location::UNKNOWN,
                Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)),
                Syntax::metavariable_rc(Location::UNKNOWN, MetaVariableId(0), vec![])
            )
        );
    }

    #[test]
    fn test_parse_metavariable_with_substitution() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "?[0 !0 !1]"),
            Syntax::metavariable_rc(
                Location::UNKNOWN,
                MetaVariableId(0),
                vec![
                    Syntax::variable_rc(Location::UNKNOWN, Index(0)),
                    Syntax::variable_rc(Location::UNKNOWN, Index(1))
                ]
            )
        );
    }

    #[test]
    fn test_parse_metavariable_no_space_between_question_and_bracket() {
        let db = Database::new();
        // "? [0]" should fail - ?[ must be a single token
        assert!(parse_syntax(&db, "? [0]").is_err());
    }

    #[test]
    fn test_parse_constant_simple() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "@42"),
            Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "42"))
        );
    }

    #[test]
    fn test_parse_constant_zero() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "@0"),
            Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "0"))
        );
    }

    #[test]
    fn test_parse_constant_large() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "@123456789"),
            Syntax::constant_rc(
                Location::UNKNOWN,
                ConstantId::from_with_db(&db, "123456789")
            )
        );
    }

    #[test]
    fn test_parse_constant_application() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "@42 @99"),
            Syntax::application_rc(
                Location::UNKNOWN,
                Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "42")),
                Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "99"))
            )
        );
    }

    #[test]
    fn test_parse_constant_with_type() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "@42 : 𝒰0"),
            Syntax::check_rc(
                Location::UNKNOWN,
                Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)),
                Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "42"))
            )
        );
    }

    #[test]
    fn test_parse_constant_in_lambda() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "λ %x → @42 %x"),
            Syntax::lambda_rc(
                Location::UNKNOWN,
                Syntax::application_rc(
                    Location::UNKNOWN,
                    Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "42")),
                    Syntax::variable_rc(Location::UNKNOWN, Index(0))
                )
            )
        );
    }

    #[test]
    fn test_parse_constant_in_pi() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "∀(%x : @42) → 𝒰0"),
            Syntax::pi_rc(
                Location::UNKNOWN,
                Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "42")),
                Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0))
            )
        );
    }

    #[test]
    fn test_parse_unbound_variable_simple() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "!0"),
            Syntax::variable_rc(Location::UNKNOWN, Index(0))
        );
    }

    #[test]
    fn test_parse_unbound_variable_higher() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "!4"),
            Syntax::variable_rc(Location::UNKNOWN, Index(4))
        );
    }

    #[test]
    fn test_parse_unbound_variable_in_lambda() {
        let db = Database::new();
        // λ %x → !0  =>  at depth 1, !0 becomes index 1
        assert_eq!(
            parse(&db, "λ %x → !0"),
            Syntax::lambda_rc(
                Location::UNKNOWN,
                Syntax::variable_rc(Location::UNKNOWN, Index(1))
            )
        );
    }

    #[test]
    fn test_parse_unbound_variable_in_nested_lambda() {
        let db = Database::new();
        // λ %x %y → !0  =>  at depth 2, !0 becomes index 2
        assert_eq!(
            parse(&db, "λ %x %y → !0"),
            Syntax::lambda_rc(
                Location::UNKNOWN,
                Syntax::lambda_rc(
                    Location::UNKNOWN,
                    Syntax::variable_rc(Location::UNKNOWN, Index(2))
                )
            )
        );
    }

    #[test]
    fn test_parse_mixed_bound_and_unbound() {
        let db = Database::new();
        // λ %x %y → %y !0  =>  %y is index 0, !0 is index 2
        assert_eq!(
            parse(&db, "λ %x %y → %y !0"),
            Syntax::lambda_rc(
                Location::UNKNOWN,
                Syntax::lambda_rc(
                    Location::UNKNOWN,
                    Syntax::application_rc(
                        Location::UNKNOWN,
                        Syntax::variable_rc(Location::UNKNOWN, Index(0)),
                        Syntax::variable_rc(Location::UNKNOWN, Index(2))
                    )
                )
            )
        );
    }

    #[test]
    fn test_parse_unbound_variable_in_pi() {
        let db = Database::new();
        // ∀(%x : 𝒰0) → !0  =>  at depth 1, !0 becomes index 1
        assert_eq!(
            parse(&db, "∀(%x : 𝒰0) → !0"),
            Syntax::pi_rc(
                Location::UNKNOWN,
                Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)),
                Syntax::variable_rc(Location::UNKNOWN, Index(1))
            )
        );
    }

    #[test]
    fn test_parse_unbound_variable_application() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "!0 !1"),
            Syntax::application_rc(
                Location::UNKNOWN,
                Syntax::variable_rc(Location::UNKNOWN, Index(0)),
                Syntax::variable_rc(Location::UNKNOWN, Index(1))
            )
        );
    }

    #[test]
    fn test_parse_print_roundtrip_unbound() {
        let db = Database::new();
        let test_cases = vec![
            ("!0", Syntax::variable_rc(Location::UNKNOWN, Index(0))),
            ("!5", Syntax::variable_rc(Location::UNKNOWN, Index(5))),
            (
                "λ %x → !0",
                Syntax::lambda_rc(
                    Location::UNKNOWN,
                    Syntax::variable_rc(Location::UNKNOWN, Index(1)),
                ),
            ),
            (
                "λ %x %y → %y !0",
                Syntax::lambda_rc(
                    Location::UNKNOWN,
                    Syntax::lambda_rc(
                        Location::UNKNOWN,
                        Syntax::application_rc(
                            Location::UNKNOWN,
                            Syntax::variable_rc(Location::UNKNOWN, Index(0)),
                            Syntax::variable_rc(Location::UNKNOWN, Index(2)),
                        ),
                    ),
                ),
            ),
            (
                "∀(%x : 𝒰0) → !0",
                Syntax::pi_rc(
                    Location::UNKNOWN,
                    Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)),
                    Syntax::variable_rc(Location::UNKNOWN, Index(1)),
                ),
            ),
            (
                "!0 !1",
                Syntax::application_rc(
                    Location::UNKNOWN,
                    Syntax::variable_rc(Location::UNKNOWN, Index(0)),
                    Syntax::variable_rc(Location::UNKNOWN, Index(1)),
                ),
            ),
        ];

        for (input, expected) in test_cases {
            let parsed = parse(&db, input);
            assert_eq!(parsed, expected, "Parse mismatch for: {}", input);
            let printed = print_syntax_to_string(&db, &parsed);
            if input.contains("!") {
                assert!(
                    printed.contains("!"),
                    "Should contain ! for: {} (got: {})",
                    input,
                    printed
                );
            }
        }
    }

    // ========== HTERM PARSING TESTS ==========

    #[test]
    fn test_parse_hconstant_simple() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "@42"),
            Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "42"))
        );
    }

    #[test]
    fn test_parse_hconstant_zero() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "@0"),
            Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "0"))
        );
    }

    #[test]
    fn test_parse_hconstant_large() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "@123456789"),
            Syntax::constant_rc(
                Location::UNKNOWN,
                ConstantId::from_with_db(&db, "123456789")
            )
        );
    }

    #[test]
    fn test_parse_hvariable_bound() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "mod %x → %x"),
            Syntax::module_rc(
                Location::UNKNOWN,
                Syntax::variable_rc(Location::UNKNOWN, Index(0))
            )
        );
    }

    #[test]
    fn test_parse_hvariable_unbound() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "!0"),
            Syntax::variable_rc(Location::UNKNOWN, Index(0))
        );
    }

    #[test]
    fn test_parse_hvariable_unbound_in_lambda() {
        let db = Database::new();
        // mod %x → !0  =>  at depth 1, !0 becomes index 1
        assert_eq!(
            parse(&db, "mod %x → !0"),
            Syntax::module_rc(
                Location::UNKNOWN,
                Syntax::variable_rc(Location::UNKNOWN, Index(1))
            )
        );
    }

    #[test]
    fn test_parse_module_single_var() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "mod %x → %x"),
            Syntax::module_rc(
                Location::UNKNOWN,
                Syntax::variable_rc(Location::UNKNOWN, Index(0))
            )
        );
    }

    #[test]
    fn test_parse_module_multiple_vars() {
        let db = Database::new();
        // mod %x %y → %x  =>  nested modules, %x at index 1
        assert_eq!(
            parse(&db, "mod %x %y → %x"),
            Syntax::module_rc(
                Location::UNKNOWN,
                Syntax::module_rc(
                    Location::UNKNOWN,
                    Syntax::variable_rc(Location::UNKNOWN, Index(1))
                )
            )
        );
    }

    #[test]
    fn test_parse_module_with_parens() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "(mod %x → %x)"),
            Syntax::module_rc(
                Location::UNKNOWN,
                Syntax::variable_rc(Location::UNKNOWN, Index(0))
            )
        );
    }

    #[test]
    fn test_parse_happlication_simple() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "@f<Bit>(@x)"),
            Syntax::happlication_rc(
                Location::UNKNOWN,
                Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "f")),
                Syntax::bit_rc(Location::UNKNOWN),
                Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "x"))
            )
        );
    }

    #[test]
    fn test_parse_happlication_chained() {
        let db = Database::new();
        // @f<Bit>(@x)<Bit>(@y)  =>  happ(happ(f, Bit, x), Bit, y)
        assert_eq!(
            parse(&db, "@f<Bit>(@x)<Bit>(@y)"),
            Syntax::happlication_rc(
                Location::UNKNOWN,
                Syntax::happlication_rc(
                    Location::UNKNOWN,
                    Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "f")),
                    Syntax::bit_rc(Location::UNKNOWN),
                    Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "x"))
                ),
                Syntax::bit_rc(Location::UNKNOWN),
                Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "y"))
            )
        );
    }

    #[test]
    fn test_parse_happlication_with_harrow_type() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "@f<Bit → Bit>(@x)"),
            Syntax::happlication_rc(
                Location::UNKNOWN,
                Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "f")),
                Syntax::harrow_rc(
                    Location::UNKNOWN,
                    Syntax::bit_rc(Location::UNKNOWN),
                    Syntax::bit_rc(Location::UNKNOWN)
                ),
                Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "x"))
            )
        );
    }

    #[test]
    fn test_parse_hcheck_simple() {
        let db = Database::new();
        // (mod %x → %x) : Bit -> Bit
        assert_eq!(
            parse(&db, "(mod %x → %x) : Bit -> Bit"),
            Syntax::check_rc(
                Location::UNKNOWN,
                Syntax::harrow_rc(
                    Location::UNKNOWN,
                    Syntax::bit_rc(Location::UNKNOWN),
                    Syntax::bit_rc(Location::UNKNOWN)
                ),
                Syntax::module_rc(
                    Location::UNKNOWN,
                    Syntax::variable_rc(Location::UNKNOWN, Index(0))
                )
            )
        );
    }

    #[test]
    fn test_parse_hcheck_with_application() {
        let db = Database::new();
        // (@42<Bit>(@99)) : Bit
        assert_eq!(
            parse(&db, "(@42<Bit>(@99)) : Bit"),
            Syntax::check_rc(
                Location::UNKNOWN,
                Syntax::bit_rc(Location::UNKNOWN),
                Syntax::happlication_rc(
                    Location::UNKNOWN,
                    Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "42")),
                    Syntax::bit_rc(Location::UNKNOWN),
                    Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "99"))
                )
            )
        );
    }

    #[test]
    fn test_parse_happlication_in_module() {
        let db = Database::new();
        // mod %f → @x<Bit>(%f)
        assert_eq!(
            parse(&db, "mod %f → @x<Bit>(%f)"),
            Syntax::module_rc(
                Location::UNKNOWN,
                Syntax::happlication_rc(
                    Location::UNKNOWN,
                    Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "x")),
                    Syntax::bit_rc(Location::UNKNOWN),
                    Syntax::variable_rc(Location::UNKNOWN, Index(0))
                )
            )
        );
    }

    #[test]
    fn test_parse_happlication_with_nested_type() {
        let db = Database::new();
        // @f<Bit → Bit → Bit>(@x)
        assert_eq!(
            parse(&db, "@f<Bit → Bit → Bit>(@x)"),
            Syntax::happlication_rc(
                Location::UNKNOWN,
                Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "f")),
                Syntax::harrow_rc(
                    Location::UNKNOWN,
                    Syntax::bit_rc(Location::UNKNOWN),
                    Syntax::harrow_rc(
                        Location::UNKNOWN,
                        Syntax::bit_rc(Location::UNKNOWN),
                        Syntax::bit_rc(Location::UNKNOWN)
                    )
                ),
                Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "x"))
            )
        );
    }

    #[test]
    fn test_parse_happlication_with_unbound_var() {
        let db = Database::new();
        // !0<Bit>(!1)
        assert_eq!(
            parse(&db, "!0<Bit>(!1)"),
            Syntax::happlication_rc(
                Location::UNKNOWN,
                Syntax::variable_rc(Location::UNKNOWN, Index(0)),
                Syntax::bit_rc(Location::UNKNOWN),
                Syntax::variable_rc(Location::UNKNOWN, Index(1))
            )
        );
    }

    #[test]
    fn test_parse_happlication_nested_in_arg() {
        let db = Database::new();
        // @42<Bit>(@99<Bit>(@100))
        assert_eq!(
            parse(&db, "@42<Bit>(@99<Bit>(@100))"),
            Syntax::happlication_rc(
                Location::UNKNOWN,
                Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "42")),
                Syntax::bit_rc(Location::UNKNOWN),
                Syntax::happlication_rc(
                    Location::UNKNOWN,
                    Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "99")),
                    Syntax::bit_rc(Location::UNKNOWN),
                    Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "100"))
                )
            )
        );
    }

    #[test]
    fn test_parse_hterm_roundtrip_examples() {
        let db = Database::new();
        let test_cases = vec![
            "@42",
            "!0",
            "mod %x → %x",
            "mod %x %y → %x",
            "@42<Bit>(@99)",
            "(mod %x → %x) : Bit → Bit",
            "mod %x → !0",
            "!0<Bit>(!1)",
        ];

        for input in test_cases {
            let parsed = parse(&db, input);
            let printed = print_syntax_to_string(&db, &parsed);
            let reparsed = parse(&db, &printed);
            assert_eq!(
                *reparsed, *parsed,
                "Round-trip failed for: {} (printed: {})",
                input, printed
            );
        }
    }

    #[test]
    fn test_parse_and_print_string_constant() {
        let db = Database::new();
        let parsed = parse(&db, "@hello");
        let printed = print_syntax_to_string(&db, &parsed);
        assert_eq!(printed, "@hello");
    }

    #[test]
    fn test_parse_and_print_numeric_constant() {
        let db = Database::new();
        let parsed = parse(&db, "@42");
        let printed = print_syntax_to_string(&db, &parsed);
        assert_eq!(printed, "@42");
    }

    #[test]
    fn test_string_interning_comprehensive() {
        let db = Database::new();
        let test_cases = vec!["@hello", "@world", "@foo", "@bar", "@hello"];
        let parsed_terms: Vec<_> = test_cases.iter().map(|s| parse(&db, s)).collect();

        for (i, term) in parsed_terms.iter().enumerate() {
            let printed = print_syntax_to_string(&db, term);
            assert_eq!(printed, test_cases[i]);
        }

        // Check string interning: first and last @hello should have same ConstantId
        if let (Syntax::Constant(c1), Syntax::Constant(c5)) =
            (parsed_terms[0].as_ref(), parsed_terms[4].as_ref())
        {
            assert_eq!(c1.name, c5.name, "String interning should reuse ID");
        } else {
            panic!("Expected constants");
        }
    }

    #[test]
    fn test_parse_bit_type() {
        let db = Database::new();
        assert_eq!(parse(&db, "Bit"), Syntax::bit_rc());
    }

    #[test]
    fn test_parse_zero_constant() {
        let db = Database::new();
        assert_eq!(parse(&db, "0"), Syntax::zero_rc());
    }

    #[test]
    fn test_parse_one_constant() {
        let db = Database::new();
        assert_eq!(parse(&db, "1"), Syntax::one_rc());
    }

    #[test]
    fn test_parse_primitives() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "$xor"),
            Syntax::prim_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "xor"))
        );
        assert_eq!(
            parse(&db, "$and"),
            Syntax::prim_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "and"))
        );
        assert_eq!(
            parse(&db, "$or"),
            Syntax::prim_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "or"))
        );
        assert_eq!(
            parse(&db, "$not"),
            Syntax::prim_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "not"))
        );
        assert_eq!(
            parse(&db, "$custom"),
            Syntax::prim_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "custom"))
        );
        assert_eq!(
            parse(&db, "$Add"),
            Syntax::prim_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "Add"))
        );
    }

    #[test]
    fn test_parse_hconstant() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "@Add"),
            Syntax::constant_rc(Location::UNKNOWN, ConstantId::from_with_db(&db, "Add"))
        );
        assert_eq!(
            parse(&db, "@Multiply"),
            Syntax::constant_rc(
                Location::UNKNOWN,
                ConstantId::from_with_db(&db, "Multiply")
            )
        );
        assert_eq!(
            parse(&db, "@MyCircuit"),
            Syntax::constant_rc(
                Location::UNKNOWN,
                ConstantId::from_with_db(&db, "MyCircuit")
            )
        );
    }

    #[test]
    fn test_parse_data_constructor_nullary() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "[@Nil]"),
            Syntax::data_constructor_rc(
                Location::UNKNOWN,
                ConstantId::from_with_db(&db, "Nil"),
                vec![]
            )
        );
    }

    #[test]
    fn test_parse_data_constructor_unary_simple() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "[@Some @42]"),
            Syntax::data_constructor_rc(
                Location::UNKNOWN,
                ConstantId::from_with_db(&db, "Some"),
                vec![Syntax::constant_rc(
                    Location::UNKNOWN,
                    ConstantId::from_with_db(&db, "42")
                )]
            )
        );
    }

    #[test]
    fn test_parse_data_constructor_unary_lambda() {
        let db = Database::new();
        // [@Some λ %0 → λ %0 → %0]
        assert_eq!(
            parse(&db, "[@Some λ %0 → λ %0 → %0]"),
            Syntax::data_constructor_rc(
                Location::UNKNOWN,
                ConstantId::from_with_db(&db, "Some"),
                vec![Syntax::lambda_rc(
                    Location::UNKNOWN,
                    Syntax::lambda_rc(
                        Location::UNKNOWN,
                        Syntax::variable_rc(Location::UNKNOWN, Index(0))
                    )
                )]
            )
        );
    }

    #[test]
    fn test_parse_data_constructor_binary_lambda() {
        let db = Database::new();
        // [@Pair (λ %0 → %0) λ %0 → %0]
        assert_eq!(
            parse(&db, "[@Pair (λ %0 → %0) λ %0 → %0]"),
            Syntax::data_constructor_rc(
                Location::UNKNOWN,
                ConstantId::from_with_db(&db, "Pair"),
                vec![
                    Syntax::lambda_rc(
                        Location::UNKNOWN,
                        Syntax::variable_rc(Location::UNKNOWN, Index(0))
                    ),
                    Syntax::lambda_rc(
                        Location::UNKNOWN,
                        Syntax::variable_rc(Location::UNKNOWN, Index(0))
                    )
                ]
            )
        );
    }

    #[test]
    fn test_case_application() {
        let db = Database::new();
        // Case scrutinee must be a variable, wrapped in a lambda to bind %x
        assert_eq!(
            parse(&db, "λ %x → %x case { @true => @1 | @false => @0 }"),
            Syntax::lambda_rc(
                Location::UNKNOWN,
                Syntax::case_rc(
                    Location::UNKNOWN,
                    Index(0),
                    vec![
                        CaseBranch::new(
                            ConstantId::from_with_db(&db, "true"),
                            0,
                            Syntax::constant_rc(
                                Location::UNKNOWN,
                                ConstantId::from_with_db(&db, "1")
                            )
                        ),
                        CaseBranch::new(
                            ConstantId::from_with_db(&db, "false"),
                            0,
                            Syntax::constant_rc(
                                Location::UNKNOWN,
                                ConstantId::from_with_db(&db, "0")
                            )
                        ),
                    ],
                )
            )
        );
    }

    #[test]
    fn test_constructor_only_patterns() {
        let db = Database::new();
        // Case scrutinee must be a variable, wrapped in a lambda to bind %x
        assert_eq!(
            parse(&db, "λ %x → %x case { @true => @1 | @false => @0 }"),
            Syntax::lambda_rc(
                Location::UNKNOWN,
                Syntax::case_rc(
                    Location::UNKNOWN,
                    Index(0),
                    vec![
                        CaseBranch::new(
                            ConstantId::from_with_db(&db, "true"),
                            0,
                            Syntax::constant_rc(
                                Location::UNKNOWN,
                                ConstantId::from_with_db(&db, "1")
                            )
                        ),
                        CaseBranch::new(
                            ConstantId::from_with_db(&db, "false"),
                            0,
                            Syntax::constant_rc(
                                Location::UNKNOWN,
                                ConstantId::from_with_db(&db, "0")
                            )
                        ),
                    ],
                )
            )
        );
    }

    #[test]
    fn test_parse_type_constructor_simple() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "#[@Bool]"),
            Syntax::type_constructor_rc(
                Location::UNKNOWN,
                ConstantId::from_with_db(&db, "Bool"),
                vec![]
            )
        );
    }

    #[test]
    fn test_parse_type_constructor_with_args() {
        let db = Database::new();
        assert_eq!(
            parse(&db, "#[@List 𝒰0]"),
            Syntax::type_constructor_rc(
                Location::UNKNOWN,
                ConstantId::from_with_db(&db, "List"),
                vec![Syntax::universe_rc(
                    Location::UNKNOWN,
                    UniverseLevel::new(0)
                )]
            )
        );
    }

    #[test]
    fn test_parse_case_no_return_type() {
        let db = Database::new();
        // λ %x → %x case { @true => @1 | @false => @0 }
        // Case scrutinee must be a variable, wrapped in a lambda to bind %x
        assert_eq!(
            parse(&db, "λ %x → %x case { @true => @1 | @false => @0 }"),
            Syntax::lambda_rc(
                Location::UNKNOWN,
                Syntax::case_rc(
                    Location::UNKNOWN,
                    Index(0),
                    vec![
                        CaseBranch::new(
                            ConstantId::from_with_db(&db, "true"),
                            0,
                            Syntax::constant_rc(
                                Location::UNKNOWN,
                                ConstantId::from_with_db(&db, "1")
                            )
                        ),
                        CaseBranch::new(
                            ConstantId::from_with_db(&db, "false"),
                            0,
                            Syntax::constant_rc(
                                Location::UNKNOWN,
                                ConstantId::from_with_db(&db, "0")
                            )
                        ),
                    ],
                )
            )
        );
    }

    #[test]
    fn test_parse_case_with_constructor_argument_pattern() {
        let db = Database::new();
        // λ %n → %n case { @Succ %m => %m }
        // Case scrutinee must be a variable, wrapped in a lambda to bind %n
        // In the branch body, %m is Index(0) (innermost binding from the pattern)
        assert_eq!(
            parse(&db, "λ %n → %n case { @Succ %m => %m }"),
            Syntax::lambda_rc(
                Location::UNKNOWN,
                Syntax::case_rc(
                    Location::UNKNOWN,
                    Index(0),
                    vec![CaseBranch::new(
                        ConstantId::from_with_db(&db, "Succ"),
                        1,
                        Syntax::variable_rc(Location::UNKNOWN, Index(0))
                    )],
                )
            )
        );
    }

    // ========== MODULE PARSING TESTS ==========

    #[test]
    fn test_parse_prim_declaration() {
        let db = Database::new();
        let module = parse_module(&db, "prim $Nat : U0;").expect("parse failed");
        assert_eq!(module.declarations.len(), 1);
        assert!(
            matches!(&module.declarations[0], Declaration::Primitive(p) if p.name.name(&db) == "Nat")
        );
    }

    #[test]
    fn test_parse_const_declaration() {
        let db = Database::new();
        let module = parse_module(&db, "const @zero : @Nat;").expect("parse failed");
        assert_eq!(module.declarations.len(), 1);
        assert!(
            matches!(&module.declarations[0], Declaration::Constant(c) if c.name.name(&db) == "zero")
        );
    }

    #[test]
    fn test_parse_tcon_declaration_no_dcons() {
        let db = Database::new();
        let module = parse_module(&db, "tcon @List (%a : U0) : -> U0;").expect("parse failed");
        assert_eq!(module.declarations.len(), 1);
        assert!(
            matches!(&module.declarations[0], Declaration::TypeConstructor(tc) if tc.name.name(&db) == "List")
        );
    }

    #[test]
    fn test_parse_tcon_declaration_with_dcons() {
        let db = Database::new();
        let input = "tcon @Option (%a : U0) : -> U0 where dcon @None : #[@Option %a] dcon @Some : %a -> #[@Option %a];";
        let module = parse_module(&db, input).expect("parse failed");
        assert_eq!(module.declarations.len(), 1);
        if let Declaration::TypeConstructor(tc) = &module.declarations[0] {
            assert_eq!(tc.name.name(&db), "Option");
            assert_eq!(tc.data_constructors.len(), 2);
            assert_eq!(tc.data_constructors[0].name.name(&db), "None");
            assert_eq!(tc.data_constructors[1].name.name(&db), "Some");
        } else {
            panic!("Expected TypeConstructor");
        }
    }

    #[test]
    fn test_parse_module_multiple_declarations() {
        let db = Database::new();
        let input = r#"
            prim $Nat : U0;
            const @zero : $Nat;
            tcon @Bool : -> U0 where dcon @True : #[@Bool] dcon @False : #[@Bool];
        "#;
        let module = parse_module(&db, input).expect("parse failed");
        assert_eq!(module.declarations.len(), 3);
        assert!(
            matches!(&module.declarations[0], Declaration::Primitive(p) if p.name.name(&db) == "Nat")
        );
        assert!(
            matches!(&module.declarations[1], Declaration::Constant(c) if c.name.name(&db) == "zero")
        );
        if let Declaration::TypeConstructor(tc) = &module.declarations[2] {
            assert_eq!(tc.name.name(&db), "Bool");
            assert_eq!(tc.data_constructors.len(), 2);
        } else {
            panic!("Expected TypeConstructor");
        }
    }

    #[test]
    fn test_parse_empty_module() {
        let db = Database::new();
        let module = parse_module(&db, "").expect("parse failed");
        assert_eq!(module.declarations.len(), 0);
    }

    #[test]
    fn test_parse_parameterized_tcon() {
        let db = Database::new();
        let module = parse_module(&db, "tcon @Option (%a : U0) : -> U0;").expect("parse failed");
        assert_eq!(module.declarations.len(), 1);
        if let Declaration::TypeConstructor(tc) = &module.declarations[0] {
            assert_eq!(tc.name.name(&db), "Option");
            assert_eq!(
                &tc.universe,
                &Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0))
            );
        } else {
            panic!("Expected TypeConstructor");
        }
    }

    #[test]
    fn test_parse_parameterized_tcon_with_dcons() {
        let db = Database::new();
        let input = r#"
            tcon @Option (%a : U0) : -> U0 where
                dcon @None : #[@Option %a]
                dcon @Some : %a -> #[@Option %a];
        "#;
        let module = parse_module(&db, input).expect("parse failed");
        assert_eq!(module.declarations.len(), 1);
        if let Declaration::TypeConstructor(tc) = &module.declarations[0] {
            assert_eq!(tc.name.name(&db), "Option");
            assert_eq!(tc.data_constructors.len(), 2);
            assert_eq!(tc.data_constructors[0].name.name(&db), "None");
            assert_eq!(tc.data_constructors[1].name.name(&db), "Some");
        } else {
            panic!("Expected TypeConstructor");
        }
    }

    #[test]
    fn test_parse_multi_param_tcon() {
        let db = Database::new();
        let module =
            parse_module(&db, "tcon @Pair (%a : U0) (%b : U0) : -> U0;").expect("parse failed");
        assert_eq!(module.declarations.len(), 1);
        if let Declaration::TypeConstructor(tc) = &module.declarations[0] {
            assert_eq!(tc.name.name(&db), "Pair");
            assert_eq!(
                &tc.universe,
                &Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0))
            );
        } else {
            panic!("Expected TypeConstructor");
        }
    }

    #[test]
    fn test_parse_tcon_no_params() {
        let db = Database::new();
        let module = parse_module(&db, "tcon @Bool : -> U0;").expect("parse failed");
        assert_eq!(module.declarations.len(), 1);
        if let Declaration::TypeConstructor(tc) = &module.declarations[0] {
            assert_eq!(tc.name.name(&db), "Bool");
            assert_eq!(
                &tc.universe,
                &Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0))
            );
        } else {
            panic!("Expected TypeConstructor");
        }
    }

    #[test]
    fn test_parse_dcon_with_params() {
        let db = Database::new();
        let input = r#"
            tcon @List (%a : U0) : -> U0 where
                dcon @Nil : #[@List %a]
                dcon @Cons (%x : %a) (%xs : #[@List %a]) : #[@List %a];
        "#;
        let module = parse_module(&db, input).expect("parse failed");
        assert_eq!(module.declarations.len(), 1);
        if let Declaration::TypeConstructor(tc) = &module.declarations[0] {
            assert_eq!(tc.name.name(&db), "List");
            assert_eq!(tc.data_constructors.len(), 2);
            assert_eq!(tc.data_constructors[0].name.name(&db), "Nil");
            assert_eq!(tc.data_constructors[1].name.name(&db), "Cons");
            // Cons type should be a Pi type
            let cons_ty_str = print_syntax_to_string(&db, &tc.data_constructors[1].full_type());
            assert!(cons_ty_str.contains("∀"), "Cons should have Pi type");
        } else {
            panic!("Expected TypeConstructor");
        }
    }

    #[test]
    fn test_parse_tcon_with_indices() {
        let db = Database::new();
        let module =
            parse_module(&db, "tcon @Vec (%a : U0) : (%n : #[@Nat]) -> U0;").expect("parse failed");
        assert_eq!(module.declarations.len(), 1);
        if let Declaration::TypeConstructor(tc) = &module.declarations[0] {
            assert_eq!(tc.name.name(&db), "Vec");
            assert_eq!(
                &tc.universe,
                &Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0))
            );
        } else {
            panic!("Expected TypeConstructor");
        }
    }

    #[test]
    fn test_module_roundtrip_simple() {
        let db = Database::new();
        let module = parse_module(&db, "prim $Nat : U0;").expect("parse failed");
        let output = crate::syn::print_module_to_string(&db, &module);
        let module2 = parse_module(&db, &output).expect("reparse failed");
        assert_eq!(module, module2);
    }

    #[test]
    fn test_module_roundtrip_complex() {
        let db = Database::new();
        let input = r#"prim $Nat : U0;
prim $Zero : $Nat;
tcon @Bool : -> U0 where
    dcon @True : #[@Bool]
    dcon @False : #[@Bool]
;
const @id : ∀ (%a : U0) (%x : %a) → %a = λ %a %x → %x;"#;
        let module = parse_module(&db, input).expect("parse failed");
        let output = crate::syn::print_module_to_string(&db, &module);
        let module2 = parse_module(&db, &output).expect("reparse failed");
        assert_eq!(module, module2);
    }

    #[test]
    fn test_module_roundtrip_with_params() {
        let db = Database::new();
        let input = r#"tcon @List (%a : U0) : -> U0 where
    dcon @Nil : #[@List %a]
    dcon @Cons (%x : %a) (%xs : #[@List %a]) : #[@List %a]
;"#;
        let module = parse_module(&db, input).expect("parse failed");
        let output = crate::syn::print_module_to_string(&db, &module);
        let module2 = parse_module(&db, &output).expect("reparse failed");
        assert_eq!(module, module2);
    }

    #[test]
    fn test_print_module_format() {
        let db = Database::new();
        let input = r#"prim $Nat : U0;
tcon @List (%a : U0) : -> U0 where
    dcon @Nil : #[@List %a]
    dcon @Cons (%x : %a) (%xs : #[@List %a]) : #[@List %a]
;"#;
        let module = parse_module(&db, input).expect("parse failed");
        let output = crate::syn::print_module_to_string(&db, &module);
        assert!(output.contains("prim $Nat : 𝒰0;"));
        // Now we print parameters, so List has (%0 : 𝒰0) after the name
        assert!(output.contains("tcon @List (%0 : 𝒰0) : -> 𝒰0 where"));
        assert!(output.contains("dcon @Nil"));
        assert!(output.contains("dcon @Cons"));
    }

    // ========== EQUALITY TYPE PARSING TESTS ==========

    #[test]
    fn test_parse_eq_type() {
        let db = Database::new();
        let parsed = parse(&db, "Eq U0 0 1");
        assert!(matches!(&*parsed, Syntax::Eq(_)));
    }

    #[test]
    fn test_parse_refl() {
        let db = Database::new();
        let parsed = parse(&db, "refl");
        assert!(matches!(&*parsed, Syntax::Refl(_)));
    }

    #[test]
    fn test_parse_transport() {
        let db = Database::new();
        let parsed = parse(&db, "transport [%0] |- %0 refl 0");
        assert!(matches!(&*parsed, Syntax::Transport(_)));
    }

    #[test]
    fn test_parse_eq_roundtrip() {
        let db = Database::new();
        let test_cases = vec![
            ("Eq U0 0 1", "Eq 𝒰0 0 1"),
            ("refl", "refl"),
            // Transport uses the new [%0] |- body syntax
            (
                "transport [%0] |- Bit refl 0",
                "transport [%0] |- Bit refl 0",
            ),
            ("Eq (Eq U0 U0 U0) refl refl", "Eq (Eq 𝒰0 𝒰0 𝒰0) refl refl"),
        ];

        for (input, expected_print) in test_cases {
            let parsed = parse(&db, input);
            let printed = print_syntax_to_string(&db, &parsed);
            assert_eq!(printed, expected_print, "Print mismatch for: {}", input);
            // Parse the printed form and verify it matches
            let reparsed = parse(&db, &printed);
            assert_eq!(
                *reparsed, *parsed,
                "Round-trip failed for: {} (printed: {})",
                input, printed
            );
        }
    }
}
