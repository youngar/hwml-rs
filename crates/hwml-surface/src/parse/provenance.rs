//! Parser provenance tracking
//!
//! Tracks the context of what is being parsed to provide rich error messages.
//! Example: "Expected ':=' while parsing definition 'foo' in namespace 'Nat'"

use crate::lex::Token;
use std::ops::Range;

/// A parsing context - tracks what operation is in progress
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParseContext {
    /// Parsing a file
    File {
        path: String,
    },
    
    /// Parsing a namespace block
    Namespace {
        name: String,
        loc: Range<usize>,
    },

    /// Parsing an open statement
    Open {
        namespace: String,
        loc: Range<usize>,
    },

    /// Parsing a def statement
    Def {
        name: String,
        loc: Range<usize>,
    },
    
    /// Parsing a meta statement
    Meta {
        name: String,
        loc: Range<usize>,
    },
    
    /// Parsing a prim statement
    Prim {
        name: String,
        loc: Range<usize>,
    },
    
    /// Parsing an inductive declaration
    Inductive {
        name: String,
        loc: Range<usize>,
    },
    
    /// Parsing a constructor within an inductive
    Constructor {
        inductive: String,
        loc: Range<usize>,
    },
    
    /// Parsing a Pi type
    PiType {
        loc: Range<usize>,
    },
    
    /// Parsing a function lambda
    FunLambda {
        loc: Range<usize>,
    },
    
    /// Parsing a let binding
    LetBinding {
        name: String,
        loc: Range<usize>,
    },
    
    /// Parsing a match expression
    MatchExpression {
        loc: Range<usize>,
    },
    
    /// Parsing a match clause
    MatchClause {
        pattern_loc: Range<usize>,
    },
    
    /// Parsing a typed binding group
    TypedBindingGroup {
        loc: Range<usize>,
    },
    
    /// Parsing an expression
    Expression {
        loc: Range<usize>,
    },
    
    /// Parsing a pattern
    Pattern {
        loc: Range<usize>,
    },
}

impl ParseContext {
    /// Get a human-readable description of this context
    pub fn description(&self) -> String {
        match self {
            ParseContext::File { path } => format!("file '{}'", path),
            ParseContext::Namespace { name, .. } => format!("namespace '{}'", name),
            ParseContext::Open { namespace, .. } => format!("open statement for '{}'", namespace),
            ParseContext::Def { name, .. } => format!("definition '{}'", name),
            ParseContext::Meta { name, .. } => format!("meta '{}'", name),
            ParseContext::Prim { name, .. } => format!("primitive '{}'", name),
            ParseContext::Inductive { name, .. } => format!("inductive type '{}'", name),
            ParseContext::Constructor { inductive, .. } => format!("constructor in '{}'", inductive),
            ParseContext::PiType { .. } => "Pi type".to_string(),
            ParseContext::FunLambda { .. } => "lambda function".to_string(),
            ParseContext::LetBinding { name, .. } => format!("let binding '{}'", name),
            ParseContext::MatchExpression { .. } => "match expression".to_string(),
            ParseContext::MatchClause { .. } => "match clause".to_string(),
            ParseContext::TypedBindingGroup { .. } => "typed binding group".to_string(),
            ParseContext::Expression { .. } => "expression".to_string(),
            ParseContext::Pattern { .. } => "pattern".to_string(),
        }
    }
    
    /// Get the location of this context
    pub fn location(&self) -> Option<Range<usize>> {
        match self {
            ParseContext::File { .. } => None,
            ParseContext::Namespace { loc, .. }
            | ParseContext::Open { loc, .. }
            | ParseContext::Def { loc, .. }
            | ParseContext::Meta { loc, .. }
            | ParseContext::Prim { loc, .. }
            | ParseContext::Inductive { loc, .. }
            | ParseContext::Constructor { loc, .. }
            | ParseContext::PiType { loc }
            | ParseContext::FunLambda { loc }
            | ParseContext::LetBinding { loc, .. }
            | ParseContext::MatchExpression { loc }
            | ParseContext::TypedBindingGroup { loc }
            | ParseContext::Expression { loc }
            | ParseContext::Pattern { loc } => Some(loc.clone()),
            ParseContext::MatchClause { pattern_loc } => Some(pattern_loc.clone()),
        }
    }
}

/// Complete provenance information for an error or AST node
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseProvenance {
    /// Stack of parsing contexts (innermost last)
    pub contexts: Vec<ParseContext>,
    
    /// Source file path (if known)
    pub file: Option<String>,
    
    /// Location where the error/node was created
    pub error_loc: Range<usize>,
    
    /// What tokens we expected (if this is an error)
    pub expected: Option<Vec<Token>>,
    
    /// What token we found instead (if this is an error)
    pub found: Option<Token>,
}

impl ParseProvenance {
    /// Create minimal provenance (just location)
    pub fn minimal(loc: Range<usize>) -> Self {
        Self {
            contexts: vec![],
            file: None,
            error_loc: loc,
            expected: None,
            found: None,
        }
    }
}
