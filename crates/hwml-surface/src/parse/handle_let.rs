//! Let expression parsing handlers
//!
//! Implements parsing for let-in expressions:
//! let x := value in expr
//! let f x y := value in expr
//! let f (x : A) : B := value in expr

use crate::lex::Token;
use crate::parse::context::Context;
use crate::parse::state::{Precedence, State};
use crate::syntax::{Bindings, Expression, Id};
use std::ops::Range;

impl Context<'_> {
    /// Handle after 'let' keyword - parse identifier name
    /// Syntax: let NAME ...
    pub(super) fn handle_let_after_keyword(&mut self, loc: Range<usize>) {
        // Expect identifier for let binding name
        if !self.at_token(Token::Identifier) {
            self.emit_error("Expected identifier after 'let'");
            let error_expr = Box::new(Expression::Error(
                crate::syntax::ExpressionError::new(loc, "Invalid let expression".to_string())
            ));
            self.push_expr(error_expr);
            return;
        }

        let name = self.parse_id();

        // Continue with bindings and type annotation parsing
        self.push_state(State::LetAfterName { loc, name });
    }

    /// Handle after parsing let name - parse bindings asynchronously
    pub(super) fn handle_let_after_name(&mut self, loc: Range<usize>, name: Id) {
        let continuation = State::LetAfterBindingsParsed { loc, name };
        self.parse_bindings_async(continuation);
    }

    /// Handle after parsing let bindings - check for optional type annotation
    pub(super) fn handle_let_after_bindings_parsed(&mut self, loc: Range<usize>, name: Id) {
        let bindings = self.pop_bindings();

        // Check for optional type annotation
        if self.at_token(Token::Colon) {
            self.consume(Token::Colon);

            // Push continuation (runs AFTER type is parsed)
            self.push_state(State::LetAfterType {
                loc,
                name,
                bindings,
                ty: None, // dummy, will pop from expr_stack
            });

            // Parse type expression asynchronously
            self.parse_expression(Precedence::Lowest);
        } else {
            // No type annotation - continue to parsing value
            self.handle_let_after_type(loc, name, bindings, None);
        }
    }

    /// Handle after parsing optional type - parse value
    pub(super) fn handle_let_after_type(
        &mut self,
        loc: Range<usize>,
        name: Id,
        bindings: Bindings,
        _ty: Option<Box<Expression>>,
    ) {
        // Pop type from expr_stack if we had one
        let ty = if _ty.is_none() && self.at_token(Token::ColonEqual) {
            // No type was parsed (we came from the else branch)
            None
        } else {
            // Type was parsed, pop it
            Some(self.pop_expr())
        };

        // Expect ':='
        if !self.at_token(Token::ColonEqual) {
            self.emit_error("Expected ':=' in let expression");
            let error_expr = Box::new(Expression::Error(
                crate::syntax::ExpressionError::new(loc, "Invalid let expression".to_string())
            ));
            self.push_expr(error_expr);
            return;
        }
        self.consume(Token::ColonEqual);

        // Push continuation (runs AFTER value is parsed)
        self.push_state(State::LetAfterValue {
            loc,
            name,
            bindings,
            ty,
        });

        // Parse value expression (runs FIRST, pushes to expr_stack)
        self.parse_expression(Precedence::Lowest);
    }

    /// Handle after parsing let value - expect 'in' and parse body
    /// Syntax: let f := VALUE in EXPR
    pub(super) fn handle_let_after_value(
        &mut self,
        loc: Range<usize>,
        name: Id,
        bindings: Bindings,
        ty: Option<Box<Expression>>,
    ) {
        // Pop the value from expr_stack
        let value = self.pop_expr();

        // Expect 'in' keyword
        if !self.at_token(Token::In) {
            self.emit_error("Expected 'in' after let value");
            let error_expr = Box::new(Expression::Error(
                crate::syntax::ExpressionError::new(loc, "Invalid let expression".to_string())
            ));
            self.push_expr(error_expr);
            return;
        }
        self.consume(Token::In);

        // Push continuation (runs AFTER body is parsed)
        self.push_state(State::LetAfterBody {
            loc,
            name,
            bindings,
            ty,
            value,
        });

        // Parse body expression (runs FIRST, pushes to expr_stack)
        self.parse_expression(Precedence::Lowest);
    }

    /// Handle after parsing let body - build LetIn node
    pub(super) fn handle_let_after_body(
        &mut self,
        loc: Range<usize>,
        name: Id,
        bindings: Bindings,
        ty: Option<Box<Expression>>,
        value: Box<Expression>,
    ) {
        // Pop the body from expr_stack
        let expr = self.pop_expr();

        // Build the LetIn node
        let end_loc = expr.loc().end;
        let let_in = Box::new(Expression::LetIn(crate::syntax::LetIn::new(
            loc.start..end_loc,
            name,
            bindings,
            ty,
            value,
            expr,
        )));

        // Push result - go through ExprFinish for precedence climbing
        self.push_state(State::ExprFinish {
            partial: let_in,
            min_prec: Precedence::Lowest,
        });
    }
}
