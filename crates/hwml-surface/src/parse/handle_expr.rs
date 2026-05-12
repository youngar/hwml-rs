//! Expression parsing handlers
//!
//! Handles expression parsing with precedence climbing.

use crate::lex::Token;
use crate::parse::context::Context;
use crate::parse::state::{State, Precedence};
use crate::syntax::{Expression, ExpressionError, ExpressionHole, App, Underscore, Paren};
use std::ops::Range;

impl<'input> Context<'input> {
    /// Handle ExprStart - begin parsing an expression at given precedence
    pub(super) fn handle_expr_start(&mut self, min_prec: Precedence) {
        let loc = self.current_location();

        // Parse atomic expression - some are synchronous, some async
        if self.at_token(Token::Identifier) {
            let id = self.parse_id();
            let expr = Box::new(Expression::Id(id));
            // Continue with precedence climbing
            self.push_state(State::ExprFinish {
                partial: expr,
                min_prec,
            });
        } else if self.at_token(Token::Number) {
            // Parse number literal
            let text = std::str::from_utf8(&self.input[loc.clone()])
                .unwrap_or("0")
                .to_string();
            self.advance();
            let expr = Box::new(Expression::Num(crate::syntax::Num::new(loc.clone(), text.into())));
            self.push_state(State::ExprFinish {
                partial: expr,
                min_prec,
            });
        } else if self.at_token(Token::LParen) {
            // ASYNC: Parenthesized expression
            self.consume(Token::LParen);
            // Push paren wrapper (runs LAST) - will pop from expr_stack and push wrapped version
            self.push_state(State::ParenAfterLParen { loc: loc.clone(), min_prec });
            // Push expression parsing (runs FIRST) - will push to expr_stack
            self.push_state(State::ExprStart { min_prec: Precedence::Lowest });
        } else if self.at_token(Token::Underscore) {
            self.consume(Token::Underscore);
            let expr = Box::new(Expression::Underscore(Underscore::new(loc.clone())));
            self.push_state(State::ExprFinish {
                partial: expr,
                min_prec,
            });
        } else if self.at_token(Token::Type) {
            self.consume(Token::Type);
            // Type or Type n - check for optional number
            let level = if self.at_token(Token::Number) {
                let num_loc = self.current_location();
                let text = std::str::from_utf8(&self.input[num_loc.clone()])
                    .unwrap_or("0");
                self.advance();
                text.parse::<u32>().ok()
            } else {
                None
            };
            let expr = Box::new(Expression::Universe(crate::syntax::Universe::new(loc.clone(), level)));
            self.push_state(State::ExprFinish {
                partial: expr,
                min_prec,
            });
        } else if self.at_token(Token::Match) {
            // ASYNC: Match expression
            self.consume(Token::Match);
            self.push_state(State::MatchStart { loc });
        } else {
            self.emit_error(format!("Expected expression, found {:?}", self.peek()));
            let expr = Box::new(Expression::Error(ExpressionError::new(loc, "Expected expression".to_string())));
            self.push_state(State::ExprFinish {
                partial: expr,
                min_prec,
            });
        }
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

    /// Handle ParenAfterLParen - wrap expression in Paren and consume closing paren
    pub(super) fn handle_paren_after_lparen(&mut self, loc: Range<usize>, min_prec: Precedence) {
        // Pop the inner expression from the expr_stack (pushed by ExprStart that just completed)
        let inner_expr = self.pop_expr();

        // Expect closing paren
        if !self.at_token(Token::RParen) {
            self.emit_error("Expected ')' after expression");
        } else {
            self.consume(Token::RParen);
        }

        // Wrap in Paren node
        let paren_expr = Box::new(Expression::Paren(Paren::new(inner_expr)));

        // Now we need to continue with precedence climbing
        // Push ExprFinish to handle operators after the paren
        self.push_state(State::ExprFinish {
            partial: paren_expr,
            min_prec,
        });
    }

    /// Helper: Get location from expression
    fn expr_loc(&self, expr: &Expression) -> Range<usize> {
        match expr {
            Expression::Id(id) => id.loc.clone(),
            Expression::App(app) => app.loc.clone(),
            Expression::Error(err) => err.loc.clone(),
            Expression::Hole(hole) => hole.loc.clone(),
            Expression::Underscore(u) => u.loc.clone(),
            _ => 0..0,
        }
    }
}
