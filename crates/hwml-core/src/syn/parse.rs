use crate::common::{DBParseError, Index, NegativeLevel};
use crate::declaration;
use crate::syn::{CaseBranch, Closure, ConstantId, RcSyntax, Syntax, Telescope};
use core::fmt::Debug;
use hwml_support::{FromWithDb, IntoWithDb};
use logos::{Lexer, Logos};
use salsa::Database;
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
#[logos(subpattern id = r"[^\p{gc=Separator}\p{gc=Control}():;,\[\]!\?\%]+")]
pub enum Token {
    #[token("∀", priority = 4)]
    #[token("forall", priority = 4)]
    Pi,
    #[token("λ", priority = 4)]
    #[token("\\", priority = 4)]
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
    #[token("->", priority = 5)]
    Arrow,
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
    #[regex(r"HW[0-9]+", priority = 4, callback = |lex| lex.slice()["HW".len()..].parse())]
    Type(usize),
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
    #[token("0", priority = 5)]
    Zero,
    #[token("1", priority = 5)]
    One,
    #[token("case", priority = 5)]
    Case,
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
    #[token("hprim", priority = 5)]
    HPrim,
    #[token("const", priority = 5)]
    Const,
    #[token("hconst", priority = 5)]
    HConst,
    #[token("tcon", priority = 5)]
    TCon,
    #[token("dcon", priority = 5)]
    DCon,
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
    ///
    /// We conceptually split this into two regions:
    /// - meta-level binders: names[0..meta_depth)
    /// - hardware-level binders: names[meta_depth..)
    ///
    /// This allows us to keep separate de Bruijn environments for
    /// meta and hardware variables while still using a single vector.
    names: Vec<String>,
    /// Number of meta-level binders currently in scope.
    meta_depth: usize,
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
            meta_depth: 0,
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

    /// Push a meta-level binder to the environment.
    fn push_name(&mut self, name: String) {
        self.push_meta_name(name);
    }

    /// Push a meta-level binder to the environment.
    fn push_meta_name(&mut self, name: String) {
        self.names.push(name);
        self.meta_depth += 1;
    }

    /// Push a hardware-level binder to the environment.
    /// This does not affect the meta-depth, only the total depth.
    fn push_hw_name(&mut self, name: String) {
        self.names.push(name);
    }

    fn extend_names<T>(&mut self, names: T)
    where
        T: IntoIterator<Item = String>,
    {
        for name in names {
            self.push_meta_name(name);
        }
    }

    /// Find a meta-level name in the environment.
    ///
    /// This only searches the meta-level region [0..meta_depth),
    /// counting indices from the end of that region.
    fn find_meta_name(&self, name: &String) -> Option<Index> {
        for (i, n) in self.names[..self.meta_depth].iter().rev().enumerate() {
            if name == n.as_str() {
                return Some(Index::new(i));
            }
        }
        None
    }

    /// Find a hardware-level name in the environment.
    ///
    /// This only searches the hardware region [meta_depth..),
    /// counting indices from the end of that region.
    fn find_hw_name(&self, name: &String) -> Option<Index> {
        let hw_slice = &self.names[self.meta_depth..];
        for (i, n) in hw_slice.iter().rev().enumerate() {
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

    /// Get the current number of meta-level binders.
    fn meta_depth(&self) -> usize {
        self.meta_depth
    }

    /// Get the current number of hardware-level binders.
    fn hw_depth(&self) -> usize {
        self.names.len().saturating_sub(self.meta_depth)
    }

    /// Reset the name environment to a given depth.
    fn reset_names(&mut self, depth: usize) {
        self.names.truncate(depth);
        // Ensure meta_depth never exceeds the total depth.
        if self.meta_depth > depth {
            self.meta_depth = depth;
        }
    }

    /// Parse with additional variables in scope.
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

fn p_semicolon_opt(state: &mut State) -> ParseResult<Option<()>> {
    p_token_opt(state, Token::Semicolon)
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

fn p_metavariable_id(state: &mut State) -> ParseResult<usize> {
    match state.peek_token() {
        Some(Ok(Token::Number(n))) => {
            state.advance_token();
            Ok(n)
        }
        Some(Ok(Token::Zero)) => {
            state.advance_token();
            Ok(0)
        }
        Some(Ok(Token::One)) => {
            state.advance_token();
            Ok(1)
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

fn p_closure_opt<'db>(state: &mut State<'db>) -> ParseResult<Option<Closure<'db>>> {
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
fn p_hatom_opt<'db>(state: &mut State<'db>) -> ParseResult<Option<RcSyntax<'db>>> {
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
                            // HardwareUniverse lambdas introduce hardware-level binders.
                            state.push_hw_name(var)
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
                    result = HSyntax::Module_rc(result);
                }
                Ok(Some(result))
            }
            Token::Variable(name) => {
                state.advance_token();
                // Otherwise, look it up in the environment
                match state.find_hw_name(&name) {
                    Some(index) => Ok(Some(HSyntax::hvariable_rc(index))),
                    _ => Err(Error::UnknownVariable(name)),
                }
            }
            Token::UnboundVariable(negative_level) => {
                state.advance_token();
                // Convert negative level to index using the hardware depth only:
                // index = hw_depth + negative_level
                let index = negative_level.to_index(state.hw_depth());
                Ok(Some(HSyntax::hvariable_rc(index)))
            }
            Token::Constant(name) => {
                state.advance_token();
                Ok(Some(HSyntax::hconstant_rc_from(state.db(), &name)))
            }
            Token::Splice => {
                state.advance_token();
                let tm = p_atom(state)?;
                Ok(Some(HSyntax::splice_rc(tm)))
            }
            Token::Zero => {
                state.advance_token();
                Ok(Some(HSyntax::zero_rc()))
            }
            Token::One => {
                state.advance_token();
                Ok(Some(HSyntax::one_rc()))
            }
            Token::Primitive(name) => {
                state.advance_token();
                Ok(Some(HSyntax::hprim_rc(name.into_with_db(state.db))))
            }
            _ => Ok(None),
        },
        None => Ok(None),
    }
}

fn p_hatom<'db>(state: &mut State<'db>) -> ParseResult<RcSyntax<'db>> {
    match p_hatom_opt(state) {
        Err(err) => Err(err),
        Ok(None) => Err(Error::MissingTerm),
        Ok(Some(term)) => Ok(term),
    }
}

// Parse application (left-associative): a b c => (a b) c
fn p_happlication_opt<'db>(state: &mut State<'db>) -> ParseResult<Option<RcSyntax<'db>>> {
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

fn p_happlication<'db>(state: &mut State<'db>) -> ParseResult<RcSyntax<'db>> {
    match p_happlication_opt(state) {
        Ok(None) => Err(Error::MissingTerm),
        Ok(Some(term)) => Ok(term),
        Err(err) => Err(err),
    }
}

fn p_hcheck_opt<'db>(state: &mut State<'db>) -> ParseResult<Option<RcSyntax<'db>>> {
    let term = p_happlication(state)?;

    // Check if there's a colon
    // The type annotation is a meta-level hardware type (Syntax of type Type)
    if let Some(()) = p_colon_opt(state)? {
        // Parse a hardware type (meta-level syntax like Bit, Bit -> Bit)
        let ty = p_hwtype(state)?;
        Ok(Some(HSyntax::hcheck_rc(ty, term)))
    } else {
        Ok(Some(term))
    }
}

/// Parse a hardware type (something of type Type).
/// This is a meta-level term, not a hardware term.
/// HardwareUniverse types include: Bit, (Bit -> Bit), variables, etc.
fn p_hwtype<'db>(state: &mut State<'db>) -> ParseResult<RcSyntax<'db>> {
    // HardwareUniverse types are parsed using the same grammar as meta-level terms
    // up to hardware arrows
    match p_harrow_opt(state) {
        Ok(None) => Err(Error::MissingTerm),
        Ok(Some(term)) => Ok(term),
        Err(err) => Err(err),
    }
}

fn p_hterm_opt<'db>(state: &mut State<'db>) -> ParseResult<Option<RcSyntax<'db>>> {
    p_hcheck_opt(state)
}

fn p_hterm<'db>(state: &mut State<'db>) -> ParseResult<RcSyntax<'db>> {
    match p_hterm_opt(state) {
        Err(err) => Err(err),
        Ok(None) => Err(Error::MissingTerm),
        Ok(Some(term)) => Ok(term),
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
                state.advance_token();
                let depth = state.names_depth();
                let mut i = 0;
                loop {
                    match p_variable_opt(state) {
                        Err(e) => return Err(e),
                        Ok(Some(var)) => {
                            i = i + 1;
                            // Meta-level lambda: introduce meta-level binders.
                            state.push_meta_name(var)
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
            Token::LBracket => {
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
                Ok(Some(Syntax::data_constructor_rc(constructor, arguments)))
            }
            Token::LHashBracket => {
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
                Ok(Some(Syntax::type_constructor_rc(constructor, arguments)))
            }
            Token::Variable(name) => {
                state.advance_token();
                // Otherwise, look it up in the environment
                match state.find_meta_name(&name) {
                    Some(index) => Ok(Some(Syntax::variable_rc(index))),
                    _ => Err(Error::UnknownVariable(name)),
                }
            }
            Token::UnboundVariable(negative_level) => {
                state.advance_token();
                // Convert negative level to index using only the meta depth:
                // index = meta_depth + negative_level
                let index = negative_level.to_index(state.meta_depth());
                Ok(Some(Syntax::variable_rc(index)))
            }
            Token::Universe(level) => {
                state.advance_token();
                Ok(Some(Syntax::universe_rc(
                    crate::common::UniverseLevel::new(level),
                )))
            }
            Token::Type(_level) => {
                state.advance_token();
                Ok(Some(Syntax::Hardware_rc()))
            }
            Token::Constant(name) => {
                state.advance_token();
                Ok(Some(Syntax::constant_rc_from(state.db(), &name)))
            }
            Token::LQuestionBracket => {
                state.advance_token();
                // Expect ?[id term1 term2 ...]
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
                Ok(Some(Syntax::metavariable_rc(
                    crate::common::MetaVariableId(id),
                    substitution,
                )))
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
            Token::Primitive(name) => {
                state.advance_token();
                if name == "Bit" {
                    Ok(Some(Syntax::bit_rc()))
                } else {
                    Ok(Some(Syntax::prim_rc_from(state.db(), &name)))
                }
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

fn p_case_motive<'db>(state: &mut State<'db>) -> ParseResult<RcSyntax<'db>> {
    // Parse the motive.
    let depth = state.names_depth();
    let var = p_variable(state)?;
    p_arrow(state)?;

    state.push_name(var);
    let result = p_harrow(state);
    state.reset_names(depth);

    result
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
    let motive = p_case_motive(state)?;
    let branches = p_case_branches(state)?;
    Ok(Some(Syntax::case_rc(lead.clone(), motive, branches)))
}

// Parse application (left-associative): a b c => (a b) c
fn p_trailing_app_opt<'db>(
    state: &mut State<'db>,
    lead: &RcSyntax<'db>,
) -> ParseResult<Option<RcSyntax<'db>>> {
    match p_atom_opt(state)? {
        None => Ok(None),
        Some(arg) => Ok(Some(Syntax::application_rc(lead.clone(), arg))),
    }
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
        Ok(Some(Syntax::harrow_rc(term, p_harrow(state)?)))
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
        Ok(Some(Syntax::check_rc(p_term(state)?, term)))
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

pub fn parse_hsyntax<'db>(db: &'db dyn Database, input: &'db str) -> ParseResult<RcSyntax<'db>> {
    let mut state = State::new(db, input);
    p_hterm(&mut state)
}

// ========== MODULE AND DECLARATION PARSING ==========

use crate::declaration::{Declaration, Module};

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

/// Parse a hardware primitive declaration: hprim $Name : Type;
fn p_hprim_decl<'db>(state: &mut State<'db>) -> ParseResult<Declaration<'db>> {
    // Expect 'hprim' token
    p_token(state, Token::HPrim, Error::Other)?;

    // Parse the name (hardware primitives use $Name syntax)
    let name = p_primitive(state)?;

    // Expect ':'
    p_token(state, Token::Colon, Error::MissingColon)?;

    // Parse the type
    let ty = p_term(state)?;

    // Expect ';'
    p_token(state, Token::Semicolon, Error::MissingSemicolon)?;

    Ok(Declaration::hardware_primitive(name, ty))
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

/// Parse a hardware constant declaration: hconst $Name : HardwareType = HardwareValue;
/// The type should be a hardware type (e.g., $Bit, $Bit -> $Bit).
/// The value is parsed using the hardware term parser (p_hterm).
fn p_hconst_decl<'db>(state: &mut State<'db>) -> ParseResult<Declaration<'db>> {
    // Expect 'hconst' token
    p_token(state, Token::HConst, Error::Other)?;

    // Parse the name (hardware constants use $Name syntax like primitives)
    let name = p_primitive(state)?;

    // Expect ':'
    p_token(state, Token::Colon, Error::MissingColon)?;

    // Parse the hardware type (this is still meta-level syntax for types like $Bit -> $Bit)
    let ty = p_term(state)?;

    // Expect '='
    p_token(state, Token::Equals, Error::Other)?;

    // Parse the hardware value using the hardware term parser
    let value = p_hterm(state)?;

    // Expect ';'
    p_token(state, Token::Semicolon, Error::MissingSemicolon)?;

    Ok(Declaration::hardware_constant(name, ty, value))
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
    let _param_tys = match p_telescope(state) {
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
    let _index_tys = match p_telescope(state) {
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
    let tcon_decl = Declaration::type_constructor(tcon_name, data_constructors, universe);

    Ok(vec![tcon_decl])
}

/// Parse a single declaration (any type)
fn p_declaration<'db>(state: &mut State<'db>) -> ParseResult<Option<Vec<Declaration<'db>>>> {
    match state.peek_token() {
        Some(Ok(Token::Prim)) => Ok(Some(vec![p_prim_decl(state)?])),
        Some(Ok(Token::HPrim)) => Ok(Some(vec![p_hprim_decl(state)?])),
        Some(Ok(Token::Const)) => Ok(Some(vec![p_const_decl(state)?])),
        Some(Ok(Token::HConst)) => Ok(Some(vec![p_hconst_decl(state)?])),
        Some(Ok(Token::TCon)) => Ok(Some(p_tcon_decl(state)?)),
        Some(Err(err)) => Err(err.clone()),
        _ => Ok(None),
    }
}

/// Parse a module (list of declarations)
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
    use crate::common::{Index, UniverseLevel};
    use crate::syn::*;

    #[test]
    fn test_parse_lambda_single_var() {
        // Test parsing: λ %0 → %0
        let db = crate::Database::new();
        let input = "λ %0 → %0";
        let result = parse_syntax(&db, input);

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
        let db = crate::Database::new();
        let input = "λ %x %y → %x";
        let result = parse_syntax(&db, input);

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
        let db = crate::Database::new();
        let input = "(λ %0 → %0)";
        let result = parse_syntax(&db, input);

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
        let db = crate::Database::new();
        let input = "∀(%x : 𝒰0) → 𝒰0";
        let result = parse_syntax(&db, input);

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
        let db = crate::Database::new();
        let input = "𝒰0";
        let result = parse_syntax(&db, input);

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
        let db = crate::Database::new();
        let result = parse_syntax(&db, input);

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
        let db = crate::Database::new();
        let input = "λ %f %x → %f %x";
        let result = parse_syntax(&db, input);

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
        let db = crate::Database::new();
        let input = "λ %f %x %y → %f %x %y";
        let result = parse_syntax(&db, input);

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
        let db = crate::Database::new();
        let input = "(λ %x → %x) : 𝒰0";
        let result = parse_syntax(&db, input);

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
        let db = crate::Database::new();
        let input = "(λ %f %x → %f %x) : 𝒰0";
        let result = parse_syntax(&db, input);

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
        let db = crate::Database::new();
        let input = "λ %x → (λ %y → %y) %x";
        let result = parse_syntax(&db, input);

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
        // Test parsing: ?[0]
        use crate::Database;
        let db = Database::default();
        let input = "?[0]";
        let result = parse_syntax(&db, input);

        assert!(result.is_ok(), "Failed to parse metavariable: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: ?[0] with ID 0
        use crate::common::MetaVariableId;
        let expected = Syntax::metavariable_rc(MetaVariableId(0), vec![]);

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_metavariable_multiple() {
        use crate::Database;
        let db = Database::default();
        let input = "?[0] ?[1] ?[0]";
        let result = parse_syntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse multiple metavariables: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: (?[0] ?[1]) ?[0]
        // Application is left-associative
        use crate::common::MetaVariableId;
        let expected = Syntax::application_rc(
            Syntax::application_rc(
                Syntax::metavariable_rc(MetaVariableId(0), vec![]),
                Syntax::metavariable_rc(MetaVariableId(1), vec![]),
            ),
            Syntax::metavariable_rc(MetaVariableId(0), vec![]),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_metavariable_in_lambda() {
        // Test parsing: λ %x → ?[0] %x
        use crate::Database;
        let db = Database::default();
        let input = "λ %x → ?[0] %x";
        let result = parse_syntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse metavariable in lambda: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: λ %x → ?[0] %x
        use crate::common::MetaVariableId;
        let expected = Syntax::lambda_rc(Syntax::application_rc(
            Syntax::metavariable_rc(MetaVariableId(0), vec![]),
            Syntax::variable_rc(Index(0)),
        ));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_metavariable_ordering() {
        // Test parsing: ?[0] ?[1] ?[2]
        let input = "?[0] ?[1] ?[2]";
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse metavariable ordering: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: (?[0] ?[1]) ?[2]
        use crate::common::MetaVariableId;
        let expected = Syntax::application_rc(
            Syntax::application_rc(
                Syntax::metavariable_rc(MetaVariableId(0), vec![]),
                Syntax::metavariable_rc(MetaVariableId(1), vec![]),
            ),
            Syntax::metavariable_rc(MetaVariableId(2), vec![]),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_metavariable_with_type() {
        // Test parsing: ?[0] : 𝒰0
        let input = "?[0] : 𝒰0";
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse metavariable with type: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: ?[0] : 𝒰0
        use crate::common::MetaVariableId;
        let expected = Syntax::check_rc(
            Syntax::universe_rc(UniverseLevel::new(0)),
            Syntax::metavariable_rc(MetaVariableId(0), vec![]),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_metavariable_with_substitution() {
        // Test parsing: ?[0 !0 !1]
        let input = "?[0 !0 !1]";
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse metavariable with substitution: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: ?[0 !0 !1]
        // !0 at depth 0 means index 0, !1 at depth 0 means index 1
        use crate::common::MetaVariableId;
        let expected = Syntax::metavariable_rc(
            MetaVariableId(0),
            vec![Syntax::variable_rc(Index(0)), Syntax::variable_rc(Index(1))],
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_metavariable_no_space_between_question_and_bracket() {
        // Test that "? [0]" (with space) doesn't parse as a metavariable
        // because ?[ must be a single token
        let input = "? [0]";
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);

        // This should fail to parse because ? is not a valid token by itself
        assert!(
            result.is_err(),
            "Expected parse error for '? [0]' but got: {:?}",
            result
        );
    }

    #[test]
    fn test_parse_constant_simple() {
        // Test parsing: @42
        let input = "@42";
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);

        assert!(result.is_ok(), "Failed to parse constant: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: @42 using string interning
        let expected = Syntax::constant_rc_from(&db, "42");

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_constant_zero() {
        // Test parsing: @0
        let input = "@0";
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);

        assert!(result.is_ok(), "Failed to parse constant @0: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: @0 using string interning
        let expected = Syntax::constant_rc_from(&db, "0");

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_constant_large() {
        // Test parsing: @123456789
        let input = "@123456789";
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse large constant: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: @123456789
        use crate::syn::ConstantId;
        let expected = Syntax::constant_rc(ConstantId::from_with_db(&db, "123456789"));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_constant_application() {
        // Test parsing: @42 @99
        let input = "@42 @99";
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse constant application: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: @42 @99
        use crate::syn::ConstantId;
        let expected = Syntax::application_rc(
            Syntax::constant_rc(ConstantId::from_with_db(&db, "42")),
            Syntax::constant_rc(ConstantId::from_with_db(&db, "99")),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_constant_with_type() {
        // Test parsing: @42 : 𝒰0
        let input = "@42 : 𝒰0";
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);

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
            Syntax::constant_rc(ConstantId::from_with_db(&db, "42")),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_constant_in_lambda() {
        // Test parsing: λ %x → @42 %x
        let input = "λ %x → @42 %x";
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse constant in lambda: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: λ %x → @42 %x
        use crate::syn::ConstantId;
        let expected = Syntax::lambda_rc(Syntax::application_rc(
            Syntax::constant_rc(ConstantId::from_with_db(&db, "42")),
            Syntax::variable_rc(Index(0)),
        ));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_constant_in_pi() {
        // Test parsing: ∀(%x : @42) → 𝒰0
        let input = "∀(%x : @42) → 𝒰0";
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse constant in pi: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: ∀(%x : @42) → 𝒰0
        use crate::syn::ConstantId;
        let expected = Syntax::pi_rc(
            Syntax::constant_rc(ConstantId::from_with_db(&db, "42")),
            Syntax::universe_rc(UniverseLevel::new(0)),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_unbound_variable_simple() {
        let input = "!0";
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);
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
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);
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
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);

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
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);

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
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);

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
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);

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
        use crate::Database;
        let db = Database::default();
        let result = parse_syntax(&db, input);

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

        use crate::Database;
        let db = Database::default();
        for (input, expected) in test_cases {
            let parsed = parse_syntax(&db, input).expect(&format!("Failed to parse: {}", input));
            assert_eq!(
                parsed, expected,
                "Parse result mismatch for input: {}",
                input
            );

            // Also verify that the printed form can be understood
            let printed = print_syntax_to_string(&db, &parsed);
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
        use crate::Database;
        let db = Database::default();
        let input = "@42";
        let result = parse_hsyntax(&db, input);

        assert!(result.is_ok(), "Failed to parse hconstant: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: @42
        use crate::syn::ConstantId;
        let expected = HSyntax::hconstant_rc(ConstantId::from_with_db(&db, "42"));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hconstant_zero() {
        use crate::Database;
        let db = Database::default(); // Test parsing: @0
        let input = "@0";
        let result = parse_hsyntax(&db, input);

        assert!(result.is_ok(), "Failed to parse hconstant @0: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: @0
        use crate::syn::ConstantId;
        let expected = HSyntax::hconstant_rc(ConstantId::from_with_db(&db, "0"));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hconstant_large() {
        use crate::Database;
        let db = Database::default(); // Test parsing: @123456789
        let input = "@123456789";
        let result = parse_hsyntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse large hconstant: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: @123456789
        use crate::syn::ConstantId;
        let expected = HSyntax::hconstant_rc(ConstantId::from_with_db(&db, "123456789"));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hvariable_bound() {
        use crate::Database;
        let db = Database::default(); // Test parsing: λ %x → %x
        let input = "λ %x → %x";
        let result = parse_hsyntax(&db, input);

        assert!(result.is_ok(), "Failed to parse hvariable: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: λ %x → %x
        let expected = HSyntax::Module_rc(HSyntax::hvariable_rc(Index(0)));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hvariable_unbound() {
        use crate::Database;
        let db = Database::default(); // Test parsing: !0
        let input = "!0";
        let result = parse_hsyntax(&db, input);

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
        use crate::Database;
        let db = Database::default(); // Test parsing: λ %x → !0
                                      // At depth 1, !0 should become index 1
        let input = "λ %x → !0";
        let result = parse_hsyntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse unbound hvariable in lambda: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: λ %x → !0
        // Inside the lambda (depth 1), !0 means index = 1 + 0 = 1
        let expected = HSyntax::Module_rc(HSyntax::hvariable_rc(Index(1)));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_Module_single_var() {
        use crate::Database;
        let db = Database::default(); // Test parsing: λ %x → %x
        let input = "λ %x → %x";
        let result = parse_hsyntax(&db, input);

        assert!(result.is_ok(), "Failed to parse Module: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: λ %x → %x
        let expected = HSyntax::Module_rc(HSyntax::hvariable_rc(Index(0)));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_Module_multiple_vars() {
        use crate::Database;
        let db = Database::default(); // Test parsing: λ %x %y → %x
                                      // This creates nested lambdas: λ %x → (λ %y → %x)
                                      // In the innermost body, %x has index 1 (skip over %y to reach %x)
        let input = "λ %x %y → %x";
        let result = parse_hsyntax(&db, input);

        assert!(result.is_ok(), "Failed to parse Module: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: λ %x → λ %y → %x
        // %x is at index 1 in the innermost scope
        let expected = HSyntax::Module_rc(HSyntax::Module_rc(HSyntax::hvariable_rc(Index(1))));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_Module_with_parens() {
        use crate::Database;
        let db = Database::default(); // Test parsing: (λ %x → %x)
        let input = "(λ %x → %x)";
        let result = parse_hsyntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse Module with parens: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: λ %x → %x
        let expected = HSyntax::Module_rc(HSyntax::hvariable_rc(Index(0)));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_happlication_simple() {
        use crate::Database;
        let db = Database::default(); // Test parsing: λ %f %x → %f %x
                                      // We need variables to be bound, so we use a lambda expression
        let input = "λ %f %x → %f %x";
        let result = parse_hsyntax(&db, input);

        assert!(result.is_ok(), "Failed to parse happlication: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: λ %f → λ %x → %f %x
        // %f is at index 1 (skip over %x), %x is at index 0
        let expected = HSyntax::Module_rc(HSyntax::Module_rc(HSyntax::happlication_rc(
            HSyntax::hvariable_rc(Index(1)),
            HSyntax::hvariable_rc(Index(0)),
        )));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_happlication_left_associative() {
        use crate::Database;
        let db = Database::default(); // Test parsing: λ %f %x %y → %f %x %y
                                      // This should parse as: λ %f → λ %x → λ %y → ((%f %x) %y)
                                      // Application is left-associative
        let input = "λ %f %x %y → %f %x %y";
        let result = parse_hsyntax(&db, input);

        assert!(result.is_ok(), "Failed to parse happlication: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: λ %f → λ %x → λ %y → ((%f %x) %y)
        // %f is at index 2, %x is at index 1, %y is at index 0
        let expected = HSyntax::Module_rc(HSyntax::Module_rc(HSyntax::Module_rc(
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
        use crate::Database;
        let db = Database::default(); // Test parsing: @42 @99
        let input = "@42 @99";
        let result = parse_hsyntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse happlication with constants: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: @42 @99
        use crate::syn::ConstantId;
        let expected = HSyntax::happlication_rc(
            HSyntax::hconstant_rc(ConstantId::from_with_db(&db, "42")),
            HSyntax::hconstant_rc(ConstantId::from_with_db(&db, "99")),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hcheck_simple() {
        use crate::Database;
        let db = Database::default();
        // Test parsing: (λ %x → %x) : $Bit -> $Bit
        // The type annotation is a hardware type (meta-level Syntax of type Type)
        let input = "(λ %x → %x) : $Bit -> $Bit";
        let result = parse_hsyntax(&db, input);

        assert!(result.is_ok(), "Failed to parse hcheck: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: (λ %x → %x) : $Bit -> $Bit
        let hw_type = Syntax::harrow_rc(Syntax::bit_rc(), Syntax::bit_rc());
        let expected =
            HSyntax::hcheck_rc(hw_type, HSyntax::Module_rc(HSyntax::hvariable_rc(Index(0))));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hcheck_with_application() {
        use crate::Database;
        let db = Database::default();
        // Test parsing: (@42 @99) : $Bit
        // The type annotation is a hardware type
        let input = "(@42 @99) : $Bit";
        let result = parse_hsyntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse hcheck with application: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: (@42 @99) : $Bit
        use crate::syn::ConstantId;
        let expected = HSyntax::hcheck_rc(
            Syntax::bit_rc(),
            HSyntax::happlication_rc(
                HSyntax::hconstant_rc(ConstantId::from_with_db(&db, "42")),
                HSyntax::hconstant_rc(ConstantId::from_with_db(&db, "99")),
            ),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_splice_simple() {
        // Test parsing: ~@42
        use crate::Database;
        let db = Database::default();
        let input = "~@42";
        let result = parse_hsyntax(&db, input);

        assert!(result.is_ok(), "Failed to parse splice: {:?}", result);

        let parsed = result.unwrap();

        // Build expected: ~@42
        use crate::syn::ConstantId;
        let expected = HSyntax::splice_rc(Syntax::constant_rc(ConstantId::from_with_db(&db, "42")));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_splice_with_lambda() {
        // Test parsing: ~(λ %x → %x)
        use crate::Database;
        let db = Database::default();
        let input = "~(λ %x → %x)";
        let result = parse_hsyntax(&db, input);

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
        use crate::Database;
        let db = Database::default();
        let input = "~𝒰0";
        let result = parse_hsyntax(&db, input);

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
        use crate::Database;
        let db = Database::default(); // Test parsing: λ %f → (λ %x → %f %x) @42
                                      // This applies an inner lambda to a constant
        let input = "λ %f → (λ %x → %f %x) @42";
        let result = parse_hsyntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse complex nested hterm: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: λ %f → (λ %x → %f %x) @42
        use crate::syn::ConstantId;
        let expected = HSyntax::Module_rc(HSyntax::happlication_rc(
            HSyntax::Module_rc(HSyntax::happlication_rc(
                HSyntax::hvariable_rc(Index(1)), // %f
                HSyntax::hvariable_rc(Index(0)), // %x
            )),
            HSyntax::hconstant_rc(ConstantId::from_with_db(&db, "42")),
        ));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hterm_mixed_bound_unbound() {
        use crate::Database;
        let db = Database::default(); // Test parsing: λ %x %y → %y !0
                                      // %y is bound (index 0), !0 is unbound (index 2 at depth 2)
        let input = "λ %x %y → %y !0";
        let result = parse_hsyntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse mixed bound and unbound hterm: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: λ %x → λ %y → %y !0
        // %y has index 0, !0 has index 2
        let expected = HSyntax::Module_rc(HSyntax::Module_rc(HSyntax::happlication_rc(
            HSyntax::hvariable_rc(Index(0)),
            HSyntax::hvariable_rc(Index(2)),
        )));

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hterm_splice_in_application() {
        use crate::Database;
        let db = Database::default(); // Test parsing: @42 ~𝒰0
        let input = "@42 ~𝒰0";
        let result = parse_hsyntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse splice in application: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: @42 ~𝒰0
        use crate::syn::ConstantId;
        let expected = HSyntax::happlication_rc(
            HSyntax::hconstant_rc(ConstantId::from_with_db(&db, "42")),
            HSyntax::splice_rc(Syntax::universe_rc(UniverseLevel::new(0))),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hterm_check_with_splice() {
        use crate::Database;
        let db = Database::default();
        // Test parsing: ~@42 : $Bit
        // The type annotation is a hardware type (meta-level Syntax)
        let input = "~@42 : $Bit";
        let result = parse_hsyntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse check with splice: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: ~@42 : $Bit
        use crate::syn::ConstantId;
        let expected = HSyntax::hcheck_rc(
            Syntax::bit_rc(),
            HSyntax::splice_rc(Syntax::constant_rc(ConstantId::from_with_db(&db, "42"))),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hterm_unbound_variables_multiple() {
        use crate::Database;
        let db = Database::default(); // Test parsing: !0 !1 !2
        let input = "!0 !1 !2";
        let result = parse_hsyntax(&db, input);

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
        use crate::Database;
        let db = Database::default(); // Test parsing: @42 (@99 @100)
                                      // Should parse as: @42 (@99 @100), not (@42 @99) @100
        let input = "@42 (@99 @100)";
        let result = parse_hsyntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse parentheses precedence: {:?}",
            result
        );

        let parsed = result.unwrap();

        // Build expected: @42 (@99 @100)
        use crate::syn::ConstantId;
        let expected = HSyntax::happlication_rc(
            HSyntax::hconstant_rc(ConstantId::from_with_db(&db, "42")),
            HSyntax::happlication_rc(
                HSyntax::hconstant_rc(ConstantId::from_with_db(&db, "99")),
                HSyntax::hconstant_rc(ConstantId::from_with_db(&db, "100")),
            ),
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_hterm_roundtrip_examples() {
        use crate::syn::print::print_hsyntax_to_string;
        use crate::Database;
        let db = Database::default();

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
            let parsed = parse_hsyntax(&db, input).expect(&format!("Failed to parse: {}", input));

            // Also verify that the printed form can be understood
            let printed = print_hsyntax_to_string(&db, &parsed);

            // The printed form should be parseable
            let reparsed = parse_hsyntax(&db, &printed);
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

    #[test]
    fn test_parse_and_print_string_constant() {
        // Test that parsing and printing string constants works correctly
        use crate::Database;
        let db = Database::default();
        let input = "@hello";
        let parsed = parse_syntax(&db, input).expect("Failed to parse @hello");

        // Print it back to string
        use crate::syn::print::print_syntax_to_string;
        let printed = print_syntax_to_string(&db, &parsed);

        // Should print back as @hello
        assert_eq!(printed, "@hello");
    }

    #[test]
    fn test_parse_and_print_numeric_constant() {
        // Test that parsing and printing numeric constants works correctly
        use crate::Database;
        let db = Database::default();
        let input = "@42";
        let parsed = parse_syntax(&db, input).expect("Failed to parse @42");

        // Print it back to string
        use crate::syn::print::print_syntax_to_string;
        let printed = print_syntax_to_string(&db, &parsed);

        // Should print back as @42
        assert_eq!(printed, "@42");
    }

    #[test]
    fn test_string_interning_comprehensive() {
        // Test that string interning works correctly with multiple constants
        let test_cases = vec![
            "@hello", "@world", "@foo", "@bar", "@hello", // Duplicate - should reuse same ID
        ];

        use crate::Database;
        let db = Database::default();
        let mut parsed_terms = Vec::new();
        for input in &test_cases {
            let parsed = parse_syntax(&db, input).expect(&format!("Failed to parse {}", input));
            parsed_terms.push(parsed);
        }

        // Print them all back
        use crate::syn::print::print_syntax_to_string;
        for (i, term) in parsed_terms.iter().enumerate() {
            let printed = print_syntax_to_string(&db, term);
            assert_eq!(printed, test_cases[i]);
        }

        // Test that the first and last @hello have the same ConstantId (string interning working)
        if let (Syntax::Constant(c1), Syntax::Constant(c5)) =
            (parsed_terms[0].as_ref(), parsed_terms[4].as_ref())
        {
            assert_eq!(
                c1.name, c5.name,
                "String interning should reuse the same ID for '@hello'"
            );
        } else {
            panic!("Expected constants");
        }
    }

    #[test]
    fn test_parse_bit_type() {
        use crate::Database;
        let db = Database::default();
        let input = "$Bit";
        let result = parse_syntax(&db, input);

        assert!(result.is_ok(), "Failed to parse Bit type: {:?}", result);

        let parsed = result.unwrap();
        let expected = Syntax::bit_rc();

        assert_eq!(parsed, expected, "Parsed Bit does not match expected");
    }

    #[test]
    fn test_parse_zero_constant() {
        use crate::Database;
        let db = Database::default();
        let input = "0";
        let result = parse_hsyntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse Zero constant: {:?}",
            result
        );

        let parsed = result.unwrap();
        let expected = HSyntax::zero_rc();

        assert_eq!(parsed, expected, "Parsed Zero does not match expected");
    }

    #[test]
    fn test_parse_one_constant() {
        use crate::Database;
        let db = Database::default();
        let input = "1";
        let result = parse_hsyntax(&db, input);

        assert!(result.is_ok(), "Failed to parse One constant: {:?}", result);

        let parsed = result.unwrap();
        let expected = HSyntax::one_rc();

        assert_eq!(parsed, expected, "Parsed One does not match expected");
    }

    #[test]
    fn test_parse_quoted_zero_one() {
        use crate::Database;
        let db = Database::default();

        // Test quoted zero: '0
        let input = "'0";
        let result = parse_syntax(&db, input);
        assert!(result.is_ok(), "Failed to parse quoted zero: {:?}", result);

        let parsed = result.unwrap();
        let expected = Syntax::quote_rc(HSyntax::zero_rc());
        assert_eq!(
            parsed, expected,
            "Parsed quoted Zero does not match expected"
        );

        // Test quoted one: '1
        let input = "'1";
        let result = parse_syntax(&db, input);
        assert!(result.is_ok(), "Failed to parse quoted one: {:?}", result);

        let parsed = result.unwrap();
        let expected = Syntax::quote_rc(HSyntax::one_rc());
        assert_eq!(
            parsed, expected,
            "Parsed quoted One does not match expected"
        );
    }

    #[test]
    fn test_parse_primitives() {
        use crate::Database;
        let db = Database::default();

        // Test parsing various primitives
        let tests = vec![
            ("$xor", "xor"),
            ("$and", "and"),
            ("$or", "or"),
            ("$not", "not"),
            ("$custom", "custom"),
            ("$Add", "Add"),
        ];

        for (input, expected_name) in tests {
            let result = parse_hsyntax(&db, input);
            assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result);

            let parsed = result.unwrap();
            let expected = HSyntax::hprim_rc(expected_name.into_with_db(&db));

            assert_eq!(
                parsed, expected,
                "Parsed '{}' does not match expected",
                input
            );
        }
    }

    #[test]
    fn test_parse_hconstant() {
        use crate::Database;
        let db = Database::default();

        // Test parsing hardware constants
        let tests = vec![
            ("@Add", "Add"),
            ("@Multiply", "Multiply"),
            ("@MyCircuit", "MyCircuit"),
        ];

        for (input, expected_name) in tests {
            let result = parse_hsyntax(&db, input);
            assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result);

            let parsed = result.unwrap();
            let expected = HSyntax::hconstant_rc(expected_name.into_with_db(&db));

            assert_eq!(
                parsed, expected,
                "Parsed '{}' does not match expected",
                input
            );
        }
    }

    #[test]
    fn test_parse_data_constructor_nullary() {
        use crate::Database;
        let db = Database::default();
        let input = "[@Nil]";
        let result = parse_syntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse data constructor: {:?}",
            result
        );

        let parsed = result.unwrap();
        let expected = Syntax::data_constructor_rc(ConstantId::from_with_db(&db, "Nil"), vec![]);

        assert_eq!(
            parsed, expected,
            "Parsed data constructor does not match expected"
        );
    }

    #[test]
    fn test_parse_data_constructor_unary_simple() {
        use crate::Database;
        let db = Database::default();
        let input = "[@Some @42]";
        let result = parse_syntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse data constructor: {:?}",
            result
        );

        let parsed = result.unwrap();
        let expected = Syntax::data_constructor_rc(
            ConstantId::from_with_db(&db, "Some"),
            vec![Syntax::constant_rc(ConstantId::from_with_db(&db, "42"))],
        );

        assert_eq!(
            parsed, expected,
            "Parsed data constructor does not match expected"
        );
    }

    #[test]
    fn test_parse_data_constructor_unary_lambda() {
        use crate::Database;
        let db = Database::default();
        let input = "[@Some λ %0 → λ %0 → %0]";
        let result = parse_syntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse data constructor: {:?}",
            result
        );

        let parsed = result.unwrap();
        let expected = Syntax::data_constructor_rc(
            ConstantId::from_with_db(&db, "Some"),
            vec![Syntax::lambda_rc(Syntax::lambda_rc(Syntax::variable_rc(
                Index(0),
            )))],
        );

        assert_eq!(
            parsed, expected,
            "Parsed data constructor does not match expected"
        );
    }

    #[test]
    fn test_parse_data_constructor_binary_lambda() {
        use crate::Database;
        let db = Database::default();
        let input = "[@Pair (λ %0 → %0) λ %0 → %0]";
        let result = parse_syntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse data constructor: {:?}",
            result
        );

        let parsed = result.unwrap();
        let expected = Syntax::data_constructor_rc(
            ConstantId::from_with_db(&db, "Pair"),
            vec![
                Syntax::lambda_rc(Syntax::variable_rc(Index(0))),
                Syntax::lambda_rc(Syntax::variable_rc(Index(0))),
            ],
        );

        assert_eq!(
            parsed, expected,
            "Parsed data constructor does not match expected"
        );
    }

    #[test]
    fn test_case_application() {
        use crate::Database;
        let db = Database::default();
        // Test parsing a case expression with scrutinee
        let input = "@x case %0 → @Bool { @true => @1 | @false => @0 }";

        let parsed = parse_syntax(&db, input).expect("Failed to parse case expression");

        let expected = Syntax::case_rc(
            Syntax::constant_rc(ConstantId::from_with_db(&db, "x")),
            Syntax::constant_rc_from(&db, "Bool"),
            vec![
                CaseBranch::new(
                    ConstantId::from_with_db(&db, "true"),
                    0,
                    Syntax::constant_rc(ConstantId::from_with_db(&db, "1")),
                ),
                CaseBranch::new(
                    ConstantId::from_with_db(&db, "false"),
                    0,
                    Syntax::constant_rc(ConstantId::from_with_db(&db, "0")),
                ),
            ],
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_constructor_only_patterns() {
        use crate::Database;
        let db = Database::default();

        // Test that we can only parse constructor patterns, not variables or wildcards
        let input = "@x case %0 → @Bool { @true => @1 | @false => @0 }";

        let parsed = parse_syntax(&db, input).expect("Failed to parse constructor-only case");

        let expected = Syntax::case_rc(
            Syntax::constant_rc(ConstantId::from_with_db(&db, "x")),
            Syntax::constant_rc_from(&db, "Bool"),
            vec![
                CaseBranch::new(
                    ConstantId::from_with_db(&db, "true"),
                    0,
                    Syntax::constant_rc(ConstantId::from_with_db(&db, "1")),
                ),
                CaseBranch::new(
                    ConstantId::from_with_db(&db, "false"),
                    0,
                    Syntax::constant_rc(ConstantId::from_with_db(&db, "0")),
                ),
            ],
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_type_constructor_simple() {
        use crate::Database;
        let db = Database::default();
        let input = "#[@Bool]";
        let result = parse_syntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse type constructor: {:?}",
            result
        );

        let parsed = result.unwrap();
        let expected = Syntax::type_constructor_rc(ConstantId::from_with_db(&db, "Bool"), vec![]);

        assert_eq!(
            parsed, expected,
            "Parsed type constructor does not match expected"
        );
    }

    #[test]
    fn test_parse_type_constructor_with_args() {
        use crate::Database;
        let db = Database::default();
        let input = "#[@List 𝒰0]";
        let result = parse_syntax(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse type constructor with args: {:?}",
            result
        );

        let parsed = result.unwrap();
        let expected = Syntax::type_constructor_rc(
            ConstantId::from_with_db(&db, "List"),
            vec![Syntax::universe_rc(crate::common::UniverseLevel::new(0))],
        );

        assert_eq!(
            parsed, expected,
            "Parsed type constructor does not match expected"
        );
    }

    #[test]
    fn test_parse_case_with_type_constructor_motive() {
        use crate::Database;
        let db = Database::default();
        let input = "@x case %0 → #[@Bool] { @true => @1 | @false => @0 }";

        let parsed =
            parse_syntax(&db, input).expect("Failed to parse case with type constructor motive");

        let expected = Syntax::case_rc(
            Syntax::constant_rc(ConstantId::from_with_db(&db, "x")),
            Syntax::type_constructor_rc(ConstantId::from_with_db(&db, "Bool"), vec![]),
            vec![
                CaseBranch::new(
                    ConstantId::from_with_db(&db, "true"),
                    0,
                    Syntax::constant_rc(ConstantId::from_with_db(&db, "1")),
                ),
                CaseBranch::new(
                    ConstantId::from_with_db(&db, "false"),
                    0,
                    Syntax::constant_rc(ConstantId::from_with_db(&db, "0")),
                ),
            ],
        );

        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_parse_case_with_constructor_argument_pattern() {
        use crate::common::Index;
        use crate::Database;
        let db = Database::default();

        // Scrutinee @n, case index %0, pattern @Succ %m, body refers to %m.
        // The pattern binder %m should be available in the branch body.
        let input = "@n case %0 → @Nat { @Succ %m => %m }";

        let parsed = parse_syntax(&db, input).expect("Failed to parse case with arg pattern");

        let expected = Syntax::case_rc(
            Syntax::constant_rc(ConstantId::from_with_db(&db, "n")),
            Syntax::constant_rc_from(&db, "Nat"),
            vec![CaseBranch::new(
                ConstantId::from_with_db(&db, "Succ"),
                1,
                // In the branch body, %m should resolve to the innermost binder
                Syntax::variable_rc(Index(0)),
            )],
        );

        assert_eq!(parsed, expected);
    }

    // ========== MODULE PARSING TESTS ==========

    #[test]
    fn test_parse_prim_declaration() {
        use crate::Database;
        let db = Database::default();
        let input = "prim $Nat : U0;";
        let result = parse_module(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse primitive declaration: {:?}",
            result
        );

        let module = result.unwrap();
        assert_eq!(module.declarations.len(), 1);

        let decl = &module.declarations[0];
        assert!(matches!(decl, Declaration::Primitive(_)));
        if let Declaration::Primitive(p) = decl {
            assert_eq!(p.name.name(&db), "Nat");
        }
    }

    #[test]
    fn test_parse_hprim_declaration() {
        use crate::Database;
        let db = Database::default();
        let input = "hprim $Add : $Bit -> $Bit -> $Bit;";
        let result = parse_module(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse hardware primitive declaration: {:?}",
            result
        );

        let module = result.unwrap();
        assert_eq!(module.declarations.len(), 1);

        let decl = &module.declarations[0];
        assert!(matches!(decl, Declaration::HardwarePrimitive(_)));
        if let Declaration::HardwarePrimitive(hp) = decl {
            assert_eq!(hp.name.name(&db), "Add");
        }
    }

    #[test]
    fn test_parse_const_declaration() {
        use crate::Database;
        let db = Database::default();
        let input = "const @zero : @Nat;";
        let result = parse_module(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse constant declaration: {:?}",
            result
        );

        let module = result.unwrap();
        assert_eq!(module.declarations.len(), 1);

        let decl = &module.declarations[0];
        assert!(matches!(decl, Declaration::Constant(_)));
        if let Declaration::Constant(c) = decl {
            assert_eq!(c.name.name(&db), "zero");
        }
    }

    #[test]
    fn test_parse_tcon_declaration_no_dcons() {
        use crate::Database;
        let db = Database::default();
        let input = "tcon @List (%a : U0) : -> U0;";
        let result = parse_module(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse type constructor declaration: {:?}",
            result
        );

        let module = result.unwrap();
        assert_eq!(module.declarations.len(), 1);

        let decl = &module.declarations[0];
        assert!(matches!(decl, Declaration::TypeConstructor(_)));
        if let Declaration::TypeConstructor(tc) = decl {
            assert_eq!(tc.name.name(&db), "List");
        }
    }

    #[test]
    fn test_parse_tcon_declaration_with_dcons() {
        use crate::Database;
        let db = Database::default();
        let input =
            "tcon @Option (%a : U0) : -> U0 where dcon @None : @Option %a dcon @Some : %a -> @Option %a;";
        let result = parse_module(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse type constructor with data constructors: {:?}",
            result
        );

        let module = result.unwrap();
        assert_eq!(module.declarations.len(), 1); // 1 tcon containing 2 dcons

        assert!(matches!(
            &module.declarations[0],
            Declaration::TypeConstructor(_)
        ));
        if let Declaration::TypeConstructor(tc) = &module.declarations[0] {
            assert_eq!(tc.name.name(&db), "Option");
            assert_eq!(tc.data_constructors.len(), 2);
            assert_eq!(tc.data_constructors[0].name.name(&db), "None");
            assert_eq!(tc.data_constructors[1].name.name(&db), "Some");
        }
    }

    #[test]
    fn test_parse_module_multiple_declarations() {
        use crate::Database;
        let db = Database::default();
        let input = r#"
            prim $Nat : U0;
            hprim $Add : $Bit -> $Bit -> $Bit;
            const @zero : $Nat;
            tcon @Bool : -> U0 where dcon @True : @Bool dcon @False : @Bool;
        "#;
        let result = parse_module(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse module with multiple declarations: {:?}",
            result
        );

        let module = result.unwrap();
        assert_eq!(module.declarations.len(), 4); // prim + hprim + const + tcon (containing 2 dcons)

        assert!(matches!(&module.declarations[0], Declaration::Primitive(_)));
        if let Declaration::Primitive(p) = &module.declarations[0] {
            assert_eq!(p.name.name(&db), "Nat");
        }

        assert!(matches!(
            &module.declarations[1],
            Declaration::HardwarePrimitive(_)
        ));
        if let Declaration::HardwarePrimitive(hp) = &module.declarations[1] {
            assert_eq!(hp.name.name(&db), "Add");
        }

        assert!(matches!(&module.declarations[2], Declaration::Constant(_)));
        if let Declaration::Constant(c) = &module.declarations[2] {
            assert_eq!(c.name.name(&db), "zero");
        }

        assert!(matches!(
            &module.declarations[3],
            Declaration::TypeConstructor(_)
        ));
        if let Declaration::TypeConstructor(tc) = &module.declarations[3] {
            assert_eq!(tc.name.name(&db), "Bool");
            assert_eq!(tc.data_constructors.len(), 2);
            assert_eq!(tc.data_constructors[0].name.name(&db), "True");
            assert_eq!(tc.data_constructors[1].name.name(&db), "False");
        }
    }

    #[test]
    fn test_parse_empty_module() {
        use crate::Database;
        let db = Database::default();
        let input = "";
        let result = parse_module(&db, input);

        assert!(result.is_ok(), "Failed to parse empty module: {:?}", result);

        let module = result.unwrap();
        assert_eq!(module.declarations.len(), 0);
    }

    #[test]
    fn test_parse_parameterized_tcon() {
        // Test parsing: tcon @Option (%a : U0) : -> U0;
        use crate::Database;
        let db = Database::default();
        let input = "tcon @Option (%a : U0) : -> U0;";
        let result = parse_module(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse parameterized tcon: {:?}",
            result
        );

        let module = result.unwrap();
        assert_eq!(module.declarations.len(), 1);

        let decl = &module.declarations[0];
        assert!(matches!(decl, Declaration::TypeConstructor(_)));
        if let Declaration::TypeConstructor(tc) = decl {
            assert_eq!(tc.name.name(&db), "Option");
        }

        // The type should be: ∀ (%0 : 𝒰0) → 𝒰0
        if let Declaration::TypeConstructor(tc) = decl {
            let expected_ty = Syntax::universe_rc(UniverseLevel::new(0));
            assert_eq!(&tc.universe, &expected_ty);
        }
    }

    #[test]
    fn test_parse_parameterized_tcon_with_dcons() {
        // Test parsing:
        // tcon @Option (%a : U0) : -> U0 where
        //     dcon @None : @Option %a
        //     dcon @Some : %a -> @Option %a;
        use crate::Database;
        let db = Database::default();
        let input = r#"
            tcon @Option (%a : U0) : -> U0 where
                dcon @None : @Option %a
                dcon @Some : %a -> @Option %a;
        "#;
        let result = parse_module(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse parameterized tcon with dcons: {:?}",
            result
        );

        let module = result.unwrap();
        assert_eq!(module.declarations.len(), 1); // tcon containing 2 dcons

        // Check the type constructor
        let tcon_decl = &module.declarations[0];
        assert!(matches!(tcon_decl, Declaration::TypeConstructor(_)));
        if let Declaration::TypeConstructor(tc) = tcon_decl {
            assert_eq!(tc.name.name(&db), "Option");
            assert_eq!(tc.data_constructors.len(), 2);
            assert_eq!(tc.data_constructors[0].name.name(&db), "None");
            assert_eq!(tc.data_constructors[1].name.name(&db), "Some");
        }
    }

    #[test]
    fn test_parse_multi_param_tcon() {
        // Test parsing: tcon @Pair (%a : U0) (%b : U0) : -> U0;
        use crate::Database;
        let db = Database::default();
        let input = "tcon @Pair (%a : U0) (%b : U0) : -> U0;";
        let result = parse_module(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse multi-param tcon: {:?}",
            result
        );

        let module = result.unwrap();
        assert_eq!(module.declarations.len(), 1);

        let decl = &module.declarations[0];
        assert!(matches!(decl, Declaration::TypeConstructor(_)));
        if let Declaration::TypeConstructor(tc) = decl {
            assert_eq!(tc.name.name(&db), "Pair");
            // The universe should be 𝒰0
            let expected_ty = Syntax::universe_rc(UniverseLevel::new(0));
            assert_eq!(&tc.universe, &expected_ty);
        }
    }

    #[test]
    fn test_parse_tcon_no_params() {
        // Test parsing: tcon @Bool : -> U0;
        use crate::Database;
        let db = Database::default();
        let input = "tcon @Bool : -> U0;";
        let result = parse_module(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse tcon without params: {:?}",
            result
        );

        let module = result.unwrap();
        assert_eq!(module.declarations.len(), 1);

        let decl = &module.declarations[0];
        assert!(matches!(decl, Declaration::TypeConstructor(_)));
        if let Declaration::TypeConstructor(tc) = decl {
            assert_eq!(tc.name.name(&db), "Bool");
            // The type should be just: 𝒰0 (no Pi)
            let expected_ty = Syntax::universe_rc(UniverseLevel::new(0));
            assert_eq!(&tc.universe, &expected_ty);
        }
    }

    #[test]
    fn test_parse_dcon_with_params() {
        // Test parsing:
        // tcon @List (%a : U0) : -> U0 where
        //     dcon @Nil : @List %a
        //     dcon @Cons (%x : %a) (%xs : @List %a) : @List %a;
        use crate::Database;
        let db = Database::default();
        let input = r#"
            tcon @List (%a : U0) : -> U0 where
                dcon @Nil : @List %a
                dcon @Cons (%x : %a) (%xs : @List %a) : @List %a;
        "#;
        let result = parse_module(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse dcon with params: {:?}",
            result
        );

        let module = result.unwrap();
        assert_eq!(module.declarations.len(), 1); // 1 tcon containing 2 dcons

        // Check the type constructor
        let tcon_decl = &module.declarations[0];
        assert!(matches!(tcon_decl, Declaration::TypeConstructor(_)));
        if let Declaration::TypeConstructor(tc) = tcon_decl {
            assert_eq!(tc.name.name(&db), "List");
            assert_eq!(tc.data_constructors.len(), 2);

            // Check @Nil - should have type that references the tcon parameter
            assert_eq!(tc.data_constructors[0].name.name(&db), "Nil");

            // Check @Cons - should have parameters that become Pi types
            assert_eq!(tc.data_constructors[1].name.name(&db), "Cons");

            // The Cons type should be a nested Pi type
            // ∀ (%0 : !1) (%1 : #[@List !2]) → #[@List !2]
            // where !1 and !2 reference the tcon parameter %a
            let cons_ty_str = print_syntax_to_string(&db, &tc.data_constructors[1].full_type());
            assert!(cons_ty_str.contains("∀"), "Cons should have Pi type");
        }
    }

    #[test]
    fn test_parse_tcon_with_indices() {
        // Test parsing: tcon @Vec (%a : U0) : (%n : @Nat) -> U0;
        use crate::Database;
        let db = Database::default();
        let input = "tcon @Vec (%a : U0) : (%n : @Nat) -> U0;";
        let result = parse_module(&db, input);

        assert!(
            result.is_ok(),
            "Failed to parse tcon with indices: {:?}",
            result
        );

        let module = result.unwrap();
        assert_eq!(module.declarations.len(), 1);

        let decl = &module.declarations[0];
        assert!(matches!(decl, Declaration::TypeConstructor(_)));
        if let Declaration::TypeConstructor(tc) = decl {
            assert_eq!(tc.name.name(&db), "Vec");
            // The universe should be 𝒰0
            let expected_ty = Syntax::universe_rc(UniverseLevel::new(0));
            assert_eq!(&tc.universe, &expected_ty);
        }
    }

    #[test]
    fn test_module_roundtrip_simple() {
        use crate::Database;
        let db = Database::default();
        let input = "prim $Nat : U0;";

        // Parse
        let module = parse_module(&db, input).expect("Failed to parse");

        // Print
        let output = crate::syn::print_module_to_string(&db, &module);

        // Parse again
        let module2 = parse_module(&db, &output).expect("Failed to parse printed output");

        // Should be equal
        assert_eq!(module, module2);
    }

    #[test]
    fn test_module_roundtrip_complex() {
        use crate::Database;
        let db = Database::default();
        let input = r#"prim $Nat : U0;
prim $Zero : $Nat;
tcon @Bool : -> U0 where
    dcon @True : @Bool
    dcon @False : @Bool
;
const @id : ∀ (%a : U0) (%x : %a) → %a = λ %a %x → %x;"#;

        // Parse
        let module = parse_module(&db, input).expect("Failed to parse");

        // Print
        let output = crate::syn::print_module_to_string(&db, &module);

        // Parse again
        let module2 = parse_module(&db, &output).expect("Failed to parse printed output");

        // Should be equal
        assert_eq!(module, module2);
    }

    #[test]
    fn test_module_roundtrip_with_params() {
        use crate::Database;
        let db = Database::default();
        let input = r#"tcon @List (%a : U0) : -> U0 where
    dcon @Nil : @List %a
    dcon @Cons (%x : %a) (%xs : @List %a) : @List %a
;"#;

        // Parse
        let module = parse_module(&db, input).expect("Failed to parse");

        // Print
        let output = crate::syn::print_module_to_string(&db, &module);

        // Parse again
        let module2 = parse_module(&db, &output).expect("Failed to parse printed output");

        // Should be equal
        assert_eq!(module, module2);
    }

    #[test]
    fn test_print_module_format() {
        use crate::Database;
        let db = Database::default();
        let input = r#"prim $Nat : U0;
tcon @List (%a : U0) : -> U0 where
    dcon @Nil : @List %a
    dcon @Cons (%x : %a) (%xs : @List %a) : @List %a
;"#;

        let module = parse_module(&db, input).expect("Failed to parse");
        let output = crate::syn::print_module_to_string(&db, &module);

        // Verify the output contains expected elements
        assert!(output.contains("prim $Nat : 𝒰0;"));
        assert!(output.contains("tcon @List : -> 𝒰0 where"));
        assert!(output.contains("dcon @Nil"));
        assert!(output.contains("dcon @Cons"));
    }
}
