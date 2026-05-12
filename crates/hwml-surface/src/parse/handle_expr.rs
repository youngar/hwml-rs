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
        } else if self.at_token(Token::Let) {
            // ASYNC: Let expression
            // Syntax: let x := value in expr
            self.consume(Token::Let);
            self.push_state(State::LetAfterKeyword { loc });
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

        // Check for type ascription: expr : Type
        if min_prec <= Precedence::TypeAscription && self.at_token(Token::Colon) {
            self.consume(Token::Colon);

            // Build type ascription (right-associative)
            // a : A : B parses as a : (A : B) - though this is unusual

            // Push continuation (builds ascription after parsing type)
            self.push_state(State::TypeAscriptionAfterType {
                expr: partial,
            });

            // Parse type at same precedence (right-associative)
            self.parse_expression(Precedence::TypeAscription);
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


    /// Handle arrow after parsing RHS - build the arrow type or dependent Pi type
    /// This implements the "Parse-then-Reinterpret" pattern:
    /// - If LHS is (a : A) or an AppSeq of parenthesized ascriptions, convert to Pi
    /// - Otherwise, create a simple Arrow
    pub(super) fn handle_arrow_after_rhs(&mut self, lhs: Box<Expression>) {
        let rhs = self.pop_expr();

        // Check if LHS can be reinterpreted as telescope bindings
        if let Some(bindings) = self.try_convert_to_telescope_bindings(&lhs) {
            // Build Pi type: (a : A) (b : B) -> C
            let start = lhs.loc();
            let end = rhs.loc();
            let pi = Box::new(Expression::Pi(crate::syntax::Pi::new(
                start.start..end.end,
                bindings,
                rhs,
            )));
            self.push_expr(pi);
        } else {
            // Build simple arrow: A -> B
            let start = lhs.loc();
            let end = rhs.loc();
            let arrow = Box::new(Expression::Arrow(crate::syntax::Arrow::new(
                start.start..end.end,
                lhs,
                rhs,
            )));
            self.push_expr(arrow);
        }
    }

    /// Handle type ascription after parsing type - build the TypeAscription node
    pub(super) fn handle_type_ascription_after_type(&mut self, expr: Box<Expression>) {
        let ty = self.pop_expr();

        // Build type ascription: expr : Type
        let start = expr.loc();
        let end = ty.loc();
        let ascription = Box::new(Expression::TypeAscription(crate::syntax::TypeAscription::new(
            start.start..end.end,
            expr,
            ty,
        )));

        self.push_expr(ascription);
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

    /// Handle after parsing telescope bindings for dependent arrow
    /// Expect '->' and parse body
    pub(super) fn handle_dependent_arrow_after_bindings_parsed(
        &mut self,
        loc: Range<usize>,
        _expr_stack_checkpoint: usize,
        _bindings_stack_checkpoint: usize,
    ) {
        // Pop typed bindings from typed_bindings_stack
        let bindings = self.pop_typed_bindings();

        // Expect '->'
        if !self.at_token(Token::Arrow) {
            self.emit_error("Expected '->' after telescope bindings");
            // Push error expression
            let error = Box::new(Expression::Error(crate::syntax::ExpressionError::new(
                loc.clone(),
                "Expected '->' after telescope bindings".to_string(),
            )));
            self.push_expr(error);
            return;
        }
        self.consume(Token::Arrow);

        // Update the DependentArrowAfterBody state on the stack with the bindings
        // Pop it, update it, and push it back
        let next_state = self.pop_state().expect("Expected DependentArrowAfterBody on stack");
        if let State::DependentArrowAfterBody { loc: body_loc, bindings: _ } = next_state {
            self.push_state(State::DependentArrowAfterBody {
                loc: body_loc,
                bindings,
            });
        } else {
            panic!("Expected DependentArrowAfterBody state, found {:?}", next_state);
        }

        // Parse the body expression
        self.parse_expression(Precedence::Lowest);
    }

    /// Handle after parsing body of dependent arrow
    /// Build Pi node with the typed bindings
    pub(super) fn handle_dependent_arrow_after_body(
        &mut self,
        loc: Range<usize>,
        bindings: crate::syntax::TypedBindings,
    ) {
        // Pop body from expr_stack
        let body = self.pop_expr();

        // Build Pi node with the typed bindings
        let end_loc = body.loc().end;
        let pi = Box::new(Expression::Pi(crate::syntax::Pi::new(
            loc.start..end_loc,
            bindings,
            body,
        )));

        // Push result through ExprFinish for precedence climbing
        self.push_state(State::ExprFinish {
            partial: pi,
            min_prec: Precedence::Lowest,
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

    /// Try to convert an expression to telescope bindings (Parse-then-Reinterpret pattern)
    /// Returns Some(TypedBindings) if the expression is:
    /// - A single parenthesized TypeAscription: (a : A)
    /// - An AppSeq of parenthesized TypeAscriptions: (a : A) (b : B)
    /// Returns None otherwise (use simple Arrow instead)
    fn try_convert_to_telescope_bindings(&self, expr: &Expression) -> Option<crate::syntax::TypedBindings> {
        use crate::syntax::{Pattern, Binder, TypedBindingGroup};

        // Helper: Extract (name, type) from a parenthesized type ascription
        let extract_binding = |e: &Expression| -> Option<(Pattern, Box<Expression>)> {
            match e {
                Expression::Paren(paren) => {
                    match &*paren.expr {
                        Expression::TypeAscription(asc) => {
                            // Extract the pattern from the LHS
                            let pattern = match &*asc.expr {
                                Expression::Id(id) => Pattern::Id(id.clone()),
                                Expression::Underscore(u) => Pattern::Underscore(u.clone()),
                                _ => return None, // Complex LHS not supported in telescopes
                            };
                            Some((pattern, asc.ty.clone()))
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        };

        // Try to convert based on expression type
        match expr {
            // Single parenthesized ascription: (a : A)
            Expression::Paren(_) => {
                if let Some((pattern, ty)) = extract_binding(expr) {
                    let loc = pattern.loc();
                    let binder = Binder::new(loc, pattern);
                    let group = TypedBindingGroup::new(vec![binder], ty);
                    Some(crate::syntax::TypedBindings::new(vec![group]))
                } else {
                    None
                }
            }

            // Application sequence: (a : A) (b : B) ...
            Expression::App(app) => {
                let mut groups = vec![];

                // Try to convert each element
                for elem in &app.elements {
                    if let Some((pattern, ty)) = extract_binding(elem) {
                        let loc = pattern.loc();
                        let binder = Binder::new(loc, pattern);
                        groups.push(TypedBindingGroup::new(vec![binder], ty));
                    } else {
                        // If any element isn't a telescope binding, fail
                        return None;
                    }
                }

                if groups.is_empty() {
                    None
                } else {
                    Some(crate::syntax::TypedBindings::new(groups))
                }
            }

            // Any other expression type -> not a telescope
            _ => None,
        }
    }
}
