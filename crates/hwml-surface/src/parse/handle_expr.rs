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
        } else if self.at_token(Token::Fun) {
            // ASYNC: Lambda expression
            self.consume(Token::Fun);
            self.push_state(State::FunAfterKeyword { loc });
        } else if self.at_token(Token::Pi) {
            // ASYNC: Pi type - dependent function type
            // Syntax: Pi (x : A) -> B  or  Pi (x y : A) (z : B) -> C
            self.consume(Token::Pi);
            self.push_state(State::PiAfterKeyword { loc });
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
    /// This is the entry point - checks if we can continue parsing
    pub(super) fn handle_expr_finish(&mut self, partial: Box<Expression>, min_prec: Precedence) {
        // Check for arrow (function type) - lowest precedence
        if min_prec <= Precedence::Lowest && self.at_token(Token::Arrow) {
            self.consume(Token::Arrow);

            // Build arrow type (right-associative)
            // A -> B -> C parses as A -> (B -> C)

            // Push continuation (builds arrow after parsing RHS)
            self.push_state(State::ArrowAfterRhs {
                lhs: partial,
            });

            // Parse RHS at same precedence (right-associative)
            self.parse_expression(Precedence::Lowest);
            return;
        }

        // Check if we should continue with application
        if min_prec <= Precedence::App && self.can_parse_app_argument() {
            // Start building application
            // Push continuation (runs AFTER next arg is parsed)
            self.push_state(State::ExprApp {
                elements: vec![partial],
                min_prec,
            });

            // Parse next argument (runs FIRST, pushes to expr_stack)
            self.parse_app_argument();
        } else {
            // No application, just push the result
            self.push_expr(partial);
        }
    }


    /// Handle arrow after parsing RHS - build the arrow type
    pub(super) fn handle_arrow_after_rhs(&mut self, lhs: Box<Expression>) {
        let rhs = self.pop_expr();

        // Build arrow expression: A -> B
        let start = lhs.loc();
        let end = rhs.loc();
        let arrow = Box::new(Expression::Arrow(crate::syntax::Arrow::new(
            start.start..end.end,
            lhs,
            rhs,
        )));

        self.push_expr(arrow);
    }


    /// Handle ExprApp - accumulate application arguments
    /// Called after parsing each argument to check for more
    pub(super) fn handle_expr_app(&mut self, mut elements: Vec<Box<Expression>>, min_prec: Precedence) {
        // Pop the latest argument from expr_stack
        let arg = self.pop_expr();
        elements.push(arg);

        // Check if we can parse another argument
        if self.can_parse_app_argument() {
            // Push continuation to accumulate more
            self.push_state(State::ExprApp {
                elements,
                min_prec,
            });

            // Parse next argument
            self.parse_app_argument();
        } else {
            // Done with application - build the App node
            let start = elements[0].loc();
            let end = elements.last().unwrap().loc();
            let app = Box::new(Expression::App(App::new(start.start..end.end, elements)));

            // IMPORTANT: Go back through ExprFinish to check for arrows!
            // This handles cases like "X Y -> Z" where the app "X Y" is
            // the LHS of an arrow type.
            self.push_state(State::ExprFinish {
                partial: app,
                min_prec,
            });
        }
    }

    /// Check if we can parse an application argument
    fn can_parse_app_argument(&self) -> bool {
        matches!(self.peek(),
            Some(Token::Identifier) | Some(Token::LParen) | Some(Token::Underscore) |
            Some(Token::Number) | Some(Token::Type)
        )
    }

    /// Parse an application argument (async - pushes to expr_stack)
    fn parse_app_argument(&mut self) {
        self.parse_expression(Precedence::Atomic);
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
