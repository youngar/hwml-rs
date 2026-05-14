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
use hwml_core::common::Icit;
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
        debug_assert!(
            !self.expr_stack.is_empty(),
            "expr_stack underflow! Current state: {:?}",
            self.state_stack.last()
        );
        self.expr_stack.pop().expect("Expression stack underflow")
    }

    pub fn pop_optional_expr(&mut self) -> Option<Box<Expression>> {
        self.expr_stack.pop()
    }

    pub fn push_bindings(&mut self, bindings: Bindings) {
        self.bindings_stack.push(bindings);
    }

    pub fn pop_bindings(&mut self) -> Bindings {
        debug_assert!(
            !self.bindings_stack.is_empty(),
            "bindings_stack underflow! Current state: {:?}",
            self.state_stack.last()
        );
        self.bindings_stack.pop().expect("Bindings stack underflow")
    }

    /// Get checkpoint (current stack depth) for expr_stack
    pub fn expr_stack_checkpoint(&self) -> usize {
        self.expr_stack.len()
    }

    /// Get checkpoint (current stack depth) for bindings_stack
    pub fn bindings_stack_checkpoint(&self) -> usize {
        self.bindings_stack.len()
    }

    pub fn push_typed_bindings(&mut self, bindings: TypedBindings) {
        self.typed_bindings_stack.push(bindings);
    }

    pub fn pop_typed_bindings(&mut self) -> TypedBindings {
        debug_assert!(
            !self.typed_bindings_stack.is_empty(),
            "typed_bindings_stack underflow! Current state: {:?}",
            self.state_stack.last()
        );
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
    /// Also supports implicit bindings: {x : Type}
    pub fn parse_bindings(&mut self) -> Bindings {
        use crate::syntax::{BindingGroup, UntypedBindingGroup, TypedBindingGroup, Binder, Pattern};

        let mut groups = vec![];

        // Check if we have bindings (starts with '(', '{', bare identifier, or underscore)
        while self.at_token(Token::LParen) ||
              self.at_token(Token::LBrace) ||
              self.at_token(Token::Underscore) ||
              (self.at_token(Token::Identifier) && !self.at_token(Token::Colon) && !self.at_token(Token::ColonEqual)) {
            if self.at_token(Token::LParen) || self.at_token(Token::LBrace) {
                // Determine if this is explicit (x : A) or implicit {x : A}
                let is_implicit = self.at_token(Token::LBrace);
                let icit = if is_implicit { Icit::Implicit } else { Icit::Explicit };

                // Consume opening delimiter
                if is_implicit {
                    self.consume(Token::LBrace);
                } else {
                    self.consume(Token::LParen);
                }

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

                    // Expect closing delimiter matching the opening
                    if is_implicit {
                        if !self.at_token(Token::RBrace) {
                            self.emit_error("Expected '}' after implicit binding");
                        } else {
                            self.consume(Token::RBrace);
                        }
                    } else {
                        if !self.at_token(Token::RParen) {
                            self.emit_error("Expected ')' after typed binding");
                        } else {
                            self.consume(Token::RParen);
                        }
                    }

                    // Add typed binding group with the correct icit
                    groups.push(BindingGroup::Typed(TypedBindingGroup::new(binders, ty, icit)));
                } else {
                    // Untyped binding group (only allowed for explicit bindings)
                    if is_implicit {
                        self.emit_error("Implicit bindings must be typed");
                    }

                    // Expect closing delimiter
                    if is_implicit {
                        if !self.at_token(Token::RBrace) {
                            self.emit_error("Expected '}' after binders");
                        } else {
                            self.consume(Token::RBrace);
                        }
                    } else {
                        if !self.at_token(Token::RParen) {
                            self.emit_error("Expected ')' or ':' after binders");
                        } else {
                            self.consume(Token::RParen);
                        }
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
    pub(super) fn parse_type_expression_sync(&mut self) -> Box<Expression> {
        let loc = self.current_location();

        // First, parse the atomic/application part
        let expr = if self.at_token(Token::Identifier) {
            let start_loc = self.current_location();
            let id = self.parse_id();
            let first_expr = Box::new(Expression::Id(id));

            // Check for application: List A, List A B, List (Option A), etc.
            let mut app_elements = vec![first_expr];
            while (self.at_token(Token::Identifier) || self.at_token(Token::LParen))
                  && !self.at_token(Token::Arrow) && !self.at_token(Token::RParen) {
                if self.at_token(Token::Identifier) {
                    let id = self.parse_id();
                    app_elements.push(Box::new(Expression::Id(id)));
                } else if self.at_token(Token::LParen) {
                    // Parenthesized sub-expression: (Option A), (A -> B), etc.
                    self.consume(Token::LParen);
                    let sub_expr = self.parse_type_expression_sync();
                    if !self.at_token(Token::RParen) {
                        self.emit_error("Expected ')' after parenthesized type");
                    } else {
                        self.consume(Token::RParen);
                    }
                    app_elements.push(sub_expr);
                }
            }

            // If we collected multiple elements, create an App
            if app_elements.len() > 1 {
                let end_loc = app_elements.last().unwrap().loc();
                Box::new(Expression::App(crate::syntax::App::new(
                    start_loc.start..end_loc.end,
                    app_elements
                )))
            } else {
                app_elements.into_iter().next().unwrap()
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
        } else if self.at_token(Token::Pi) {
            // Pi type: Pi (x : A) -> B
            self.consume(Token::Pi);

            // Parse typed bindings
            let bindings = self.parse_pi_typed_bindings_sync();

            // Expect '->'
            if !self.at_token(Token::Arrow) {
                self.emit_error("Expected '->' after Pi bindings");
                return Box::new(Expression::Error(crate::syntax::ExpressionError::new(loc, "Expected '->' after Pi bindings".to_string())));
            }
            self.consume(Token::Arrow);

            // Parse target type recursively
            let target = self.parse_type_expression_sync();
            let end_loc = target.loc().end;

            Box::new(Expression::Pi(crate::syntax::Pi::new(
                loc.start..end_loc,
                bindings,
                target,
            )))
        } else if self.at_token(Token::LParen) {
            // Parenthesized type expression: (A -> B), (Option A), etc.
            self.consume(Token::LParen);
            let expr = self.parse_type_expression_sync();
            if !self.at_token(Token::RParen) {
                self.emit_error("Expected ')' after parenthesized type");
            } else {
                self.consume(Token::RParen);
            }
            expr
        } else {
            self.emit_error("Expected type expression");
            Box::new(Expression::Error(crate::syntax::ExpressionError::new(loc, "Expected type".to_string())))
        };

        // Now check for arrow types: A -> B, (Prod A B) -> C, etc.
        // This applies to ALL atomic expressions, not just identifiers
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
    }

    /// Parse an expression - pushes result to expr_stack
    pub fn parse_expression(&mut self, min_prec: crate::parse::state::Precedence) {
        self.push_state(crate::parse::state::State::ExprStart { min_prec });
    }

    /// Check if we're at a synchronization point for error recovery (statement level)
    pub fn at_sync_point(&self) -> bool {
        matches!(self.peek(),
            Some(Token::Def) | Some(Token::Meta) | Some(Token::Prim) |
            Some(Token::Namespace) | Some(Token::Open) | Some(Token::Inductive) |
            Some(Token::RBrace) | None
        )
    }

    /// Check if we're at an expression-level synchronization point.
    ///
    /// These are tokens that typically delimit expressions and are safe places
    /// to resume parsing after an error within an expression.
    ///
    /// Expression sync points include:
    /// - Delimiters: comma, closing paren, closing brace
    /// - Expression terminators: pipe (for match), fat arrow (for match/lambda)
    /// - Statement keywords (also sync expressions)
    /// - EOF
    pub fn at_expr_sync_point(&self) -> bool {
        matches!(self.peek(),
            // Expression delimiters
            Some(Token::Comma) | Some(Token::RParen) | Some(Token::RBrace) |
            // Match/lambda terminators
            Some(Token::Pipe) | Some(Token::FatArrow) |
            // Statement keywords (always sync)
            Some(Token::Def) | Some(Token::Meta) | Some(Token::Prim) |
            Some(Token::Namespace) | Some(Token::Open) | Some(Token::Inductive) |
            // EOF
            None
        )
    }

    /// Check if current token is a pattern-level sync point.
    ///
    /// Pattern sync points include:
    /// - Match clause separators: pipe (|), fat arrow (=>)
    /// - Delimiters: comma, closing paren, closing brace
    /// - Statement keywords
    /// - EOF
    pub fn at_pattern_sync_point(&self) -> bool {
        matches!(self.peek(),
            // Pattern-specific: match clause separators
            Some(Token::Pipe) | Some(Token::FatArrow) |
            // Delimiters
            Some(Token::Comma) | Some(Token::RParen) | Some(Token::RBrace) |
            // Statement keywords (always sync)
            Some(Token::Def) | Some(Token::Meta) | Some(Token::Prim) |
            Some(Token::Namespace) | Some(Token::Open) | Some(Token::Inductive) |
            // EOF
            None
        )
    }


    /// Skip to the next expression boundary for error recovery.
    ///
    /// This is more fine-grained than skip_to_statement_boundary and allows us to
    /// recover within an expression (e.g., skip a malformed subexpression but continue
    /// parsing other parts of a tuple or application).
    ///
    /// Stops at: comma, closing paren, closing brace, pipe, fat arrow, statement keywords, or EOF.
    pub(super) fn skip_to_expr_boundary(&mut self) {
        while !self.at_end() && !self.at_expr_sync_point() {
            // Track brackets as we skip (important for correct sync)
            match self.peek() {
                Some(Token::LBrace) => {
                    let loc = self.consume(Token::LBrace);
                    self.push_brace(loc);
                }
                Some(Token::LParen) => {
                    let loc = self.consume(Token::LParen);
                    self.push_paren(loc);
                }
                _ => {
                    self.advance();
                }
            }
        }
    }

    /// Skip to the next pattern boundary for error recovery.
    ///
    /// Used when pattern parsing fails to recover at the next safe point.
    /// Stops at: pipe, fat arrow, comma, closing delimiters, statement keywords, or EOF.
    pub(super) fn skip_to_pattern_boundary(&mut self) {
        while !self.at_end() && !self.at_pattern_sync_point() {
            // Track brackets as we skip (important for correct sync)
            match self.peek() {
                Some(Token::LBrace) => {
                    let loc = self.consume(Token::LBrace);
                    self.push_brace(loc);
                }
                Some(Token::LParen) => {
                    let loc = self.consume(Token::LParen);
                    self.push_paren(loc);
                }
                _ => {
                    self.advance();
                }
            }
        }
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

    pub fn brace_depth(&self) -> usize {
        self.brace_stack.len()
    }

    pub fn push_paren(&mut self, loc: Range<usize>) {
        self.paren_stack.push(loc);
    }

    pub fn pop_paren(&mut self) -> Option<Range<usize>> {
        self.paren_stack.pop()
    }

    pub fn paren_depth(&self) -> usize {
        self.paren_stack.len()
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

    /// Parse typed bindings for Pi types (synchronous version)
    /// Pi requires ALL bindings to be typed: Pi (x : A) (y : B) -> C
    /// Also supports implicit bindings: Pi {x : A} (y : B) -> C
    fn parse_pi_typed_bindings_sync(&mut self) -> TypedBindings {
        use crate::syntax::{Binder, Pattern, TypedBindingGroup};

        let mut groups = vec![];

        // Expect at least one typed binding group: (x : A) or {x : A}
        while self.at_token(Token::LParen) || self.at_token(Token::LBrace) {
            // Determine if this is explicit (x : A) or implicit {x : A}
            let is_implicit = self.at_token(Token::LBrace);
            let icit = if is_implicit { Icit::Implicit } else { Icit::Explicit };

            // Consume opening delimiter
            if is_implicit {
                self.consume(Token::LBrace);
            } else {
                self.consume(Token::LParen);
            }

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
                    binders.push(Binder::new(
                        loc.clone(),
                        Pattern::Underscore(crate::syntax::Underscore::new(loc)),
                    ));
                }
            }

            // Expect ':' and type
            if !self.at_token(Token::Colon) {
                self.emit_error("Pi bindings must be typed: expected ':'");
                break;
            }
            self.consume(Token::Colon);

            // Parse the type
            let ty = self.parse_type_expression_sync();

            // Expect closing delimiter matching the opening
            if is_implicit {
                if !self.at_token(Token::RBrace) {
                    self.emit_error("Expected '}' after implicit binding");
                } else {
                    self.consume(Token::RBrace);
                }
            } else {
                if !self.at_token(Token::RParen) {
                    self.emit_error("Expected ')' after typed binding");
                } else {
                    self.consume(Token::RParen);
                }
            }

            // Add typed binding group with the correct icit
            groups.push(TypedBindingGroup::new(binders, ty, icit));
        }

        TypedBindings::new(groups)
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

        let program = Program::new(statements);

        // Validate AST structure in debug builds
        // This catches parser bugs by verifying structural invariants
        #[cfg(debug_assertions)]
        crate::syntax::validation::verify_program(&program);

        ParseResult {
            program,
            errors: self.errors,
        }
    }
}
