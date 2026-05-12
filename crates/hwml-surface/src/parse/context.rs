//! Parser context
//!
//! Holds all the state for the parser: tokens, stacks, errors.
//!
//! Diagnostic context is tracked via the state_stack itself - parent states
//! are continuations that remain on the stack, providing context for error messages.

use crate::lex::Token;
use crate::syntax::{
    Expression, Id, Bindings, TypedBindings, Statement, Program,
    ExpressionError, ExpressionHole, StatementError,
};
use crate::parse::state::State;
use std::ops::Range;

/// Block kind for tracking nested structures
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BlockKind {
    Namespace,
    Match,
    Inductive,
    Function,
}

/// Parser context - holds all mutable state
pub struct Context<'input> {
    // ===== Input =====

    /// Source input (for byte ranges)
    pub(super) input: &'input [u8],

    /// Source file path (for error messages)
    file_path: Option<String>,

    /// Token stream (from lexer)
    tokens: Vec<(Token, Range<usize>)>,

    /// Current position in token stream
    pub(super) position: usize,

    // ===== State Machine =====

    /// Parser state stack (states carry their own data!)
    state_stack: Vec<State>,

    // ===== Typed Result Stacks (NO generic PartialNode!) =====

    /// Expression results being built
    expr_stack: Vec<Box<Expression>>,

    /// Binding groups being built
    bindings_stack: Vec<Bindings>,

    /// Typed binding groups being built
    typed_bindings_stack: Vec<TypedBindings>,

    /// Statement results being built
    statement_stack: Vec<Statement>,

    /// Identifiers being collected
    id_stack: Vec<Id>,

    // ===== Error Handling =====

    /// Collected parse errors
    errors: Vec<ParseError>,

    // ===== Block Depth Tracking (for error recovery) =====

    /// Block context stack (namespace, match, function, etc.)
    block_depth: Vec<BlockContext>,

    /// Brace matching stack
    brace_stack: Vec<Range<usize>>,

    /// Paren matching stack
    paren_stack: Vec<Range<usize>>,
}

/// Block context for error recovery
#[derive(Clone, Debug)]
struct BlockContext {
    kind: BlockKind,
    start: Range<usize>,
}

/// Parse error
#[derive(Clone, Debug)]
pub struct ParseError {
    pub message: String,
    pub location: Range<usize>,
}

/// Result of parsing
pub struct ParseResult {
    pub program: Program,
    pub errors: Vec<ParseError>,
}

impl<'input> Context<'input> {
    /// Create a new parser context
    pub fn new(input: &'input [u8], tokens: Vec<(Token, Range<usize>)>) -> Self {
        Self {
            input,
            file_path: None,
            tokens,
            position: 0,
            state_stack: vec![],
            expr_stack: vec![],
            bindings_stack: vec![],
            typed_bindings_stack: vec![],
            statement_stack: vec![],
            id_stack: vec![],
            errors: vec![],
            block_depth: vec![],
            brace_stack: vec![],
            paren_stack: vec![],
        }
    }

    /// Set the file path for error messages
    pub fn with_file_path(mut self, path: String) -> Self {
        self.file_path = Some(path);
        self
    }

    /// Get current location
    pub fn current_location(&self) -> Range<usize> {
        if self.position < self.tokens.len() {
            self.tokens[self.position].1.clone()
        } else if let Some((_, loc)) = self.tokens.last() {
            loc.end..loc.end
        } else {
            0..0
        }
    }

    /// Check if we're at end of input
    pub fn at_end(&self) -> bool {
        self.position >= self.tokens.len()
    }

    /// Peek at current token
    pub fn peek(&self) -> Option<&Token> {
        if self.position < self.tokens.len() {
            Some(&self.tokens[self.position].0)
        } else {
            None
        }
    }

    /// Check if current token matches
    pub fn at_token(&self, tok: Token) -> bool {
        self.peek() == Some(&tok)
    }

    // ===== Token Consumption =====

    /// Consume a token, return its location
    /// Panics if token doesn't match (caller should check with at_token first)
    pub fn consume(&mut self, tok: Token) -> Range<usize> {
        assert!(self.at_token(tok), "Expected {:?}, found {:?}", tok, self.peek());
        let loc = self.tokens[self.position].1.clone();
        self.position += 1;
        loc
    }

    /// Try to consume a token, return location if successful
    pub fn consume_if(&mut self, tok: Token) -> Option<Range<usize>> {
        if self.at_token(tok) {
            Some(self.consume(tok))
        } else {
            None
        }
    }

    /// Advance to next token without checking what it is
    /// Used for error recovery
    pub fn advance(&mut self) {
        if !self.at_end() {
            self.position += 1;
        }
    }

    // ===== State Stack Operations =====

    pub fn push_state(&mut self, state: State) {
        self.state_stack.push(state);
    }

    pub fn pop_state(&mut self) -> Option<State> {
        self.state_stack.pop()
    }

    // ===== Typed Stack Operations (Type-Safe!) =====

    pub fn push_expr(&mut self, expr: Box<Expression>) {
        self.expr_stack.push(expr);
    }

    pub fn pop_expr(&mut self) -> Box<Expression> {
        self.expr_stack.pop().expect("Expression stack underflow")
    }

    pub fn pop_optional_expr(&mut self) -> Option<Box<Expression>> {
        self.expr_stack.pop()
    }

    pub fn push_bindings(&mut self, bindings: Bindings) {
        self.bindings_stack.push(bindings);
    }

    pub fn pop_bindings(&mut self) -> Bindings {
        self.bindings_stack.pop().expect("Bindings stack underflow")
    }

    pub fn push_typed_bindings(&mut self, bindings: TypedBindings) {
        self.typed_bindings_stack.push(bindings);
    }

    pub fn pop_typed_bindings(&mut self) -> TypedBindings {
        self.typed_bindings_stack.pop().expect("TypedBindings stack underflow")
    }

    pub fn push_statement(&mut self, stmt: Statement) {
        self.statement_stack.push(stmt);
    }

    pub fn pop_statement(&mut self) -> Statement {
        self.statement_stack.pop().expect("Statement stack underflow")
    }

    pub fn statement_stack_len(&self) -> usize {
        self.statement_stack.len()
    }

    pub fn push_id(&mut self, id: Id) {
        self.id_stack.push(id);
    }

    pub fn pop_id(&mut self) -> Id {
        self.id_stack.pop().expect("Id stack underflow")
    }

    // ===== High-level Parsing Helpers =====

    /// Parse bindings (parameters) - returns empty if none present
    /// Handles both typed bindings (x : Type) and untyped bindings (x)
    pub fn parse_bindings(&mut self) -> Bindings {
        use crate::syntax::{BindingGroup, UntypedBindingGroup, TypedBindingGroup, Binder, Pattern};

        let mut groups = vec![];

        // Check if we have bindings (starts with '(', bare identifier, or underscore)
        while self.at_token(Token::LParen) ||
              self.at_token(Token::Underscore) ||
              (self.at_token(Token::Identifier) && !self.at_token(Token::Colon) && !self.at_token(Token::ColonEqual)) {
            if self.at_token(Token::LParen) {
                self.consume(Token::LParen);

                // Parse binders (identifiers or underscores)
                let mut binders = vec![];
                while self.at_token(Token::Identifier) || self.at_token(Token::Underscore) {
                    if self.at_token(Token::Identifier) {
                        let id = self.parse_id();
                        let loc = id.loc.clone();
                        binders.push(Binder::new(loc, Pattern::Id(id)));
                    } else {
                        // Underscore pattern
                        let loc = self.current_location();
                        self.consume(Token::Underscore);
                        binders.push(Binder::new(loc.clone(), Pattern::Underscore(crate::syntax::Underscore::new(loc))));
                    }
                }

                // Check if this is a typed binding group (has : Type)
                if self.at_token(Token::Colon) {
                    self.consume(Token::Colon);

                    // Parse the type as an expression (types are just expressions in dependent types!)
                    let ty = self.parse_type_expression_sync();

                    // Expect )
                    if !self.at_token(Token::RParen) {
                        self.emit_error("Expected ')' after typed binding");
                    } else {
                        self.consume(Token::RParen);
                    }

                    // Add typed binding group
                    groups.push(BindingGroup::Typed(TypedBindingGroup::new(binders, ty)));
                } else {
                    // Untyped binding group
                    if !self.at_token(Token::RParen) {
                        self.emit_error("Expected ')' or ':' after binders");
                    } else {
                        self.consume(Token::RParen);
                    }

                    groups.push(BindingGroup::Untyped(UntypedBindingGroup::new(binders)));
                }
            } else if self.at_token(Token::Identifier) {
                // Bare identifier (untyped)
                let id = self.parse_id();
                let loc = id.loc.clone();
                let binder = Binder::new(loc, Pattern::Id(id));
                groups.push(BindingGroup::Untyped(UntypedBindingGroup::new(vec![binder])));
            } else if self.at_token(Token::Underscore) {
                // Bare underscore (untyped)
                let loc = self.current_location();
                self.consume(Token::Underscore);
                let binder = Binder::new(loc.clone(), Pattern::Underscore(crate::syntax::Underscore::new(loc)));
                groups.push(BindingGroup::Untyped(UntypedBindingGroup::new(vec![binder])));
            }
        }

        Bindings::new(groups)
    }

    /// Parse an expression synchronously (for use in bindings)
    /// In dependent types, types are just expressions!
    /// This handles common patterns: identifiers, applications, arrows, Type
    fn parse_type_expression_sync(&mut self) -> Box<Expression> {
        let loc = self.current_location();

        if self.at_token(Token::Identifier) {
            let start_loc = self.current_location();
            let id = self.parse_id();
            let mut expr = Box::new(Expression::Id(id));

            // Check for application: List A, List A B, etc.
            let mut app_elements = vec![expr];
            while self.at_token(Token::Identifier) && !self.at_token(Token::Arrow) && !self.at_token(Token::RParen) {
                let id = self.parse_id();
                app_elements.push(Box::new(Expression::Id(id)));
            }

            // If we collected multiple elements, create an App
            if app_elements.len() > 1 {
                let end_loc = app_elements.last().unwrap().loc();
                expr = Box::new(Expression::App(crate::syntax::App::new(
                    start_loc.start..end_loc.end,
                    app_elements
                )));
            } else {
                expr = app_elements.into_iter().next().unwrap();
            }

            // Check for arrow types: A -> B
            if self.at_token(Token::Arrow) {
                let mut types = vec![expr];
                while self.at_token(Token::Arrow) {
                    self.consume(Token::Arrow);
                    // Parse the right-hand side recursively (types are expressions!)
                    let rhs = self.parse_type_expression_sync();
                    types.push(rhs);
                }

                // Build right-associative arrow chain: A -> B -> C = A -> (B -> C)
                let mut result = types.pop().unwrap();
                while let Some(left) = types.pop() {
                    let arrow_loc = left.loc().start..result.loc().end;
                    result = Box::new(Expression::Arrow(crate::syntax::Arrow::new(arrow_loc, left, result)));
                }
                result
            } else {
                expr
            }
        } else if self.at_token(Token::Type) {
            self.consume(Token::Type);
            let level = if self.at_token(Token::Number) {
                let num_loc = self.current_location();
                let text = std::str::from_utf8(&self.input[num_loc.clone()])
                    .unwrap_or("0");
                self.advance();
                text.parse::<u32>().ok()
            } else {
                None
            };
            Box::new(Expression::Universe(crate::syntax::Universe::new(loc, level)))
        } else {
            self.emit_error("Expected type expression");
            Box::new(Expression::Error(crate::syntax::ExpressionError::new(loc, "Expected type".to_string())))
        }
    }

    /// Parse an expression - pushes result to expr_stack
    pub fn parse_expression(&mut self, min_prec: crate::parse::state::Precedence) {
        self.push_state(crate::parse::state::State::ExprStart { min_prec });
    }

    /// Check if we're at a synchronization point for error recovery
    pub fn at_sync_point(&self) -> bool {
        matches!(self.peek(),
            Some(Token::Def) | Some(Token::Meta) | Some(Token::Prim) |
            Some(Token::Namespace) | Some(Token::Open) | Some(Token::Inductive) |
            Some(Token::RBrace) | None
        )
    }

    /// Helper: Parse an identifier from token stream
    pub fn parse_id(&mut self) -> Id {
        if self.at_token(Token::Identifier) {
            let loc = self.current_location();
            let text = std::str::from_utf8(&self.input[loc.clone()])
                .unwrap_or("<invalid utf8>")
                .to_string();
            self.advance();
            Id::new(loc, text.into())
        } else {
            let loc = self.current_location();
            Id::new(loc, "<error>".into())
        }
    }



    // ===== Block Depth Tracking =====

    pub fn enter_block(&mut self, kind: BlockKind) {
        let start = self.current_location();
        self.block_depth.push(BlockContext { kind, start });
    }

    pub fn exit_block(&mut self) {
        self.block_depth.pop();
    }

    pub fn current_block_depth(&self) -> usize {
        self.block_depth.len()
    }

    pub fn current_block_kind(&self) -> Option<&BlockKind> {
        self.block_depth.last().map(|ctx| &ctx.kind)
    }

    pub fn current_brace_depth(&self) -> usize {
        self.brace_stack.len()
    }

    // ===== Brace/Paren Tracking =====

    // Note: Diagnostic context is tracked via state_stack.
    // See State::diagnostic_context() in state.rs


    pub fn push_brace(&mut self, loc: Range<usize>) {
        self.brace_stack.push(loc);
    }

    pub fn pop_brace(&mut self) -> Option<Range<usize>> {
        self.brace_stack.pop()
    }

    pub fn push_paren(&mut self, loc: Range<usize>) {
        self.paren_stack.push(loc);
    }

    pub fn pop_paren(&mut self) -> Option<Range<usize>> {
        self.paren_stack.pop()
    }

    // ===== Error Handling =====

    pub fn emit_error(&mut self, msg: impl Into<String>) {
        let mut error_msg = msg.into();

        // Scan the state stack backwards for context
        // Parent states are continuations that remain on the stack while children execute
        for state in self.state_stack.iter().rev() {
            if let Some(context) = state.diagnostic_context() {
                error_msg.push_str(&format!("\n  while {}", context));
            }
        }

        let error = ParseError {
            message: error_msg,
            location: self.current_location(),
        };
        self.errors.push(error);
    }

    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    // ===== Error Node Creation =====

    /// Create an error expression node
    pub fn make_error_expr(&self, msg: impl Into<String>) -> Box<Expression> {
        Box::new(Expression::Error(ExpressionError::new(
            self.current_location(),
            msg.into(),
        )))
    }

    /// Create a hole expression node
    pub fn make_hole_expr(&self, name: Option<String>) -> Box<Expression> {
        Box::new(Expression::Hole(ExpressionHole::new(
            self.current_location(),
            name,
        )))
    }

    /// Create an error statement node
    pub fn make_error_statement(&self, msg: impl Into<String>) -> Statement {
        Statement::Invalid(StatementError::new(
            self.current_location(),
            msg.into(),
        ))
    }

    // ===== Finalization =====

    pub fn finalize(self) -> ParseResult {
        // Collect all statements
        let statements = self.statement_stack;

        ParseResult {
            program: Program::new(statements),
            errors: self.errors,
        }
    }
}
