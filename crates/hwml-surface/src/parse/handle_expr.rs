//! Expression parsing handlers
//!
//! Handles expression parsing with precedence climbing.

use crate::lex::Token;
use crate::parse::context::Context;
use crate::parse::state::{State, Precedence};
use crate::syntax::{Expression, ExpressionError, ExpressionHole, App};
use std::ops::Range;

impl<'input> Context<'input> {
    /// Handle ExprStart - begin parsing an expression at given precedence
    pub(super) fn handle_expr_start(&mut self, min_prec: Precedence) {
        let loc = self.current_location();

        // Parse atomic expression
        let expr = if self.at_token(Token::Identifier) {
            let id = self.parse_id();
            Box::new(Expression::Id(id))
        } else if self.at_token(Token::LParen) {
            self.consume(Token::LParen);
            self.parse_expression(Precedence::Lowest);
            if self.at_token(Token::RParen) {
                self.consume(Token::RParen);
            }
            self.pop_expr()
        } else if self.at_token(Token::Underscore) {
            self.consume(Token::Underscore);
            Box::new(Expression::Hole(ExpressionHole::new(loc, None)))
        } else {
            self.emit_error(format!("Expected expression, found {:?}", self.peek()));
            Box::new(Expression::Error(ExpressionError::new(loc, "Expected expression".to_string())))
        };

        // Continue with precedence climbing
        self.push_state(State::ExprFinish {
            partial: expr,
            min_prec,
        });
    }

    /// Handle ExprFinish - finish parsing expression with precedence climbing
    pub(super) fn handle_expr_finish(&mut self, mut partial: Box<Expression>, min_prec: Precedence) {
        // Build application sequence if we see more identifiers
        let mut elements = vec![partial];

        loop {
            match self.peek() {
                Some(Token::Identifier) if min_prec <= Precedence::App => {
                    // Application
                    let arg_id = self.parse_id();
                    elements.push(Box::new(Expression::Id(arg_id)));
                }
                _ => break,
            }
        }

        // If we collected multiple elements, create an App
        let result = if elements.len() > 1 {
            let start = self.expr_loc(&elements[0]);
            let end = self.expr_loc(elements.last().unwrap());
            Box::new(Expression::App(App::new(start.start..end.end, elements)))
        } else {
            elements.into_iter().next().unwrap()
        };

        self.push_expr(result);
    }

    /// Helper: Get location from expression
    fn expr_loc(&self, expr: &Expression) -> Range<usize> {
        match expr {
            Expression::Id(id) => id.loc.clone(),
            Expression::App(app) => app.loc.clone(),
            Expression::Error(err) => err.loc.clone(),
            Expression::Hole(hole) => hole.loc.clone(),
            _ => 0..0,
        }
    }
}
