//! Parser state machine
//!
//! Each state carries all the data it needs to continue parsing.
//! This eliminates the need for a generic "PartialNode" stack.

use crate::syntax::{Expression, Id, Bindings, TypedBindings, Statement, Constructor};
use std::ops::Range;

/// Parser state - each variant carries the data accumulated so far
#[derive(Clone, Debug)]
pub enum State {
    // ===== Top-level =====
    
    /// Start parsing a program
    Program,
    
    /// Parse a statement
    Statement,
    
    // ===== Namespace =====

    /// Start parsing namespace - consumes tokens and sets up body parsing
    NamespaceStart {
        loc: Range<usize>,
        name: Id,
    },

    /// Parsing namespace body - loops until RBrace, collecting statements
    NamespaceBody {
        loc: Range<usize>,
        name: Id,
        statement_stack_depth: usize,  // Track stack depth when we started
    },

    /// End parsing namespace - consumes RBrace and constructs Namespace statement
    NamespaceEnd {
        loc: Range<usize>,
        name: Id,
        statement_stack_depth: usize,  // Stack depth when namespace started
    },
    
    // ===== Def Statement =====
    
    /// Start parsing def
    DefStart {
        loc: Range<usize>,
    },
    
    /// After parsing def name
    DefAfterName {
        loc: Range<usize>,
        name: Id,
    },
    
    /// After parsing bindings (optional)
    DefAfterBindings {
        loc: Range<usize>,
        name: Id,
        bindings: Bindings,
    },
    
    /// After parsing type annotation (optional)
    DefAfterType {
        loc: Range<usize>,
        name: Id,
        bindings: Bindings,
        ty: Box<Expression>,
    },
    
    /// After parsing value - ready to construct Def
    DefAfterValue {
        loc: Range<usize>,
        name: Id,
        bindings: Bindings,
        ty: Option<Box<Expression>>,
        // value is on expr_stack
    },
    
    // ===== Meta Statement (similar to Def) =====
    
    MetaStart {
        loc: Range<usize>,
    },
    
    MetaAfterName {
        loc: Range<usize>,
        name: Id,
    },
    
    MetaAfterBindings {
        loc: Range<usize>,
        name: Id,
        bindings: Bindings,
    },
    
    MetaAfterType {
        loc: Range<usize>,
        name: Id,
        bindings: Bindings,
        ty: Box<Expression>,
    },
    
    MetaAfterValue {
        loc: Range<usize>,
        name: Id,
        bindings: Bindings,
        ty: Option<Box<Expression>>,
        // value is on expr_stack
    },
    
    // ===== Prim Statement =====
    
    PrimStart {
        loc: Range<usize>,
    },
    
    PrimAfterName {
        loc: Range<usize>,
        name: Id,
    },
    
    // After parsing type - ready to construct Prim
    PrimAfterType {
        loc: Range<usize>,
        name: Id,
        // ty is on expr_stack
    },
    
    // ===== Inductive =====
    
    InductiveStart {
        loc: Range<usize>,
    },
    
    InductiveAfterName {
        loc: Range<usize>,
        name: Id,
    },
    
    InductiveAfterParams {
        loc: Range<usize>,
        name: Id,
        params: TypedBindings,
    },
    
    InductiveAfterIndices {
        loc: Range<usize>,
        name: Id,
        params: TypedBindings,
        indices: TypedBindings,
    },
    
    InductiveConstructors {
        loc: Range<usize>,
        name: Id,
        params: TypedBindings,
        indices: TypedBindings,
        universe: Box<Expression>,
        constructors: Vec<Constructor>,
    },
    
    // Parsing a constructor
    Constructor {
        inductive_name: String,
    },

    // ===== Expressions =====

    /// Start parsing expression
    ExprStart {
        min_prec: Precedence,
    },

    /// Finish parsing expression (for precedence climbing)
    ExprFinish {
        partial: Box<Expression>,
        min_prec: Precedence,
    },

    /// Building application - accumulating arguments
    /// After parsing one argument, check for more
    ExprApp {
        elements: Vec<Box<Expression>>,  // Accumulated app elements
        min_prec: Precedence,
    },

    /// After opening paren, before parsing inner expression
    ParenAfterLParen {
        loc: Range<usize>,
        min_prec: Precedence,  // Original precedence context
    },

    /// After 'Pi' keyword
    PiAfterKeyword {
        loc: Range<usize>,
    },

    /// After parsing Pi bindings
    PiAfterBindings {
        loc: Range<usize>,
        bindings: TypedBindings,
    },

    /// After parsing LHS of arrow type (A -> ...)
    ArrowAfterRhs {
        lhs: Box<Expression>,
        // rhs is on expr_stack
    },

    /// After 'fun' keyword
    FunAfterKeyword {
        loc: Range<usize>,
    },

    /// After parsing fun bindings - need to check for '=>' and parse body
    FunAfterBindingsParsed {
        loc: Range<usize>,
    },

    /// After parsing fun body - build Fun node
    FunAfterBody {
        loc: Range<usize>,
        bindings: Bindings,
    },

    /// After 'let' keyword
    LetAfterKeyword {
        loc: Range<usize>,
    },

    /// After parsing let name
    LetAfterName {
        loc: Range<usize>,
        name: Id,
    },

    /// After parsing let value
    LetAfterValue {
        loc: Range<usize>,
        name: Id,
        bindings: Bindings,
        ty: Option<Box<Expression>>,
        // value is on expr_stack
    },

    /// After parsing let body (in expression)
    LetAfterBody {
        loc: Range<usize>,
        name: Id,
        bindings: Bindings,
        ty: Option<Box<Expression>>,
        value: Box<Expression>,
        // body is on expr_stack
    },

    /// After 'match' keyword
    MatchStart {
        loc: Range<usize>,
    },

    /// After parsing match scrutinee
    MatchAfterScrutinee {
        loc: Range<usize>,
        // scrutinee is on expr_stack
    },

    /// Parsing match clauses
    MatchClauses {
        loc: Range<usize>,
        scrutinee: Box<Expression>,
        clauses: Vec<crate::syntax::MatchClause>,
    },

    /// After parsing a match clause body
    MatchClauseAfterBody {
        loc: Range<usize>,
        scrutinee: Box<Expression>,
        clauses: Vec<crate::syntax::MatchClause>,
        pattern: crate::syntax::Pattern,
    },

    // ===== Bindings =====

    /// Start/continue parsing binding groups
    /// Accumulates groups until no more bindings found, then pushes to bindings_stack
    ParseBindingsStart {
        /// Accumulated binding groups parsed so far
        groups: Vec<crate::syntax::BindingGroup>,
    },

    /// After parsing type annotation in a typed binding group
    /// Builds the typed binding group and continues parsing bindings
    BindingGroupAfterType {
        /// The binders we collected (x, y, z in (x y z : Type))
        binders: Vec<crate::syntax::Binder>,
        /// Accumulated binding groups parsed so far
        groups: Vec<crate::syntax::BindingGroup>,
        /// Continuation state to return to after all bindings are parsed
        continuation: Box<State>,
    },

    // ===== Open Statement =====

    OpenStart {
        loc: Range<usize>,
    },

    OpenAfterName {
        loc: Range<usize>,
        namespace: Id,
    },
}

/// Precedence levels for expression parsing
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Precedence {
    Lowest = 0,   // Pi, Arrow, FatArrow
    App = 1,      // Application (juxtaposition)
    Dot = 2,      // Field access a.b
    Atomic = 3,   // Literals, ids, parens
}

impl Precedence {
    /// Get the next higher precedence level
    pub fn next(self) -> Self {
        match self {
            Precedence::Lowest => Precedence::App,
            Precedence::App => Precedence::Dot,
            Precedence::Dot => Precedence::Atomic,
            Precedence::Atomic => Precedence::Atomic,
        }
    }
}

impl State {
    /// Returns a human-readable context description for error messages.
    /// Only returns Some for "continuation" states that represent major context boundaries.
    /// Returns None for micro-states (intermediate parsing steps).
    pub fn diagnostic_context(&self) -> Option<String> {
        match self {
            // Statement-level contexts (continuations)
            State::NamespaceEnd { name, .. } => {
                Some(format!("in namespace '{}'", name.value))
            }
            State::DefAfterValue { name, .. } | State::DefAfterType { name, .. } => {
                Some(format!("in definition '{}'", name.value))
            }
            State::MetaAfterValue { name, .. } | State::MetaAfterType { name, .. } => {
                Some(format!("in meta '{}'", name.value))
            }
            State::PrimAfterType { name, .. } => {
                Some(format!("in primitive '{}'", name.value))
            }
            State::InductiveConstructors { name, .. } => {
                Some(format!("in inductive type '{}'", name.value))
            }

            // Expression-level contexts
            State::MatchClauses { .. } => {
                Some("in match expression".to_string())
            }
            State::FunAfterBody { .. } => {
                Some("in lambda function".to_string())
            }
            State::LetAfterValue { name, .. } => {
                Some(format!("in let binding '{}'", name.value))
            }
            State::LetAfterBody { name, .. } => {
                Some(format!("in let binding '{}'", name.value))
            }
            State::PiAfterKeyword { .. } => {
                Some("in Pi type".to_string())
            }
            State::PiAfterBindings { .. } => {
                Some("in Pi type".to_string())
            }

            // Micro-states - ignore for diagnostics
            State::Program
            | State::Statement
            | State::NamespaceStart { .. }
            | State::NamespaceBody { .. }
            | State::DefStart { .. }
            | State::DefAfterName { .. }
            | State::DefAfterBindings { .. }
            | State::MetaStart { .. }
            | State::MetaAfterName { .. }
            | State::MetaAfterBindings { .. }
            | State::PrimStart { .. }
            | State::PrimAfterName { .. }
            | State::InductiveStart { .. }
            | State::InductiveAfterName { .. }
            | State::InductiveAfterParams { .. }
            | State::InductiveAfterIndices { .. }
            | State::Constructor { .. }
            | State::ExprStart { .. }
            | State::ExprFinish { .. }
            | State::ExprApp { .. }
            | State::ArrowAfterRhs { .. }
            | State::ParenAfterLParen { .. }
            | State::FunAfterKeyword { .. }
            | State::FunAfterBindingsParsed { .. }
            | State::LetAfterKeyword { .. }
            | State::LetAfterName { .. }
            | State::MatchStart { .. }
            | State::MatchAfterScrutinee { .. }
            | State::MatchClauseAfterBody { .. }
            | State::ParseBindingsStart { .. }
            | State::BindingGroupAfterType { .. }
            | State::OpenStart { .. }
            | State::OpenAfterName { .. } => None,
        }
    }
}
