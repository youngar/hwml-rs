use crate::lex::Token;
use crate::parse::context::Context;
use crate::parse::state::{Precedence, State};
use crate::syntax::Expression;
use hwml_core::common::Icit;
use std::ops::Range;

impl Context<'_> {
    /// Handle PiAfterKeyword - parse typed bindings after 'Pi' keyword
    /// Syntax: Pi (x : A) -> B  or  Pi (x y : A) (z : B) -> C
    pub(super) fn handle_pi_after_keyword(&mut self, loc: Range<usize>) {
        // Parse typed bindings (one or more groups)
        // Pi requires ALL bindings to be typed, unlike fun which allows untyped bindings
        let bindings = self.parse_pi_typed_bindings();

        // Now expect '->' and parse the target type
        if !self.at_token(Token::Arrow) {
            self.emit_error("Expected '->' after Pi bindings");
            // Try to recover: push an error expression and finish
            let err = Box::new(Expression::Error(crate::syntax::ExpressionError::new(
                loc.clone(),
                "Expected '->' after Pi bindings".to_string(),
            )));
            self.push_expr(err);
            return;
        }

        self.consume(Token::Arrow);

        // Push continuation (runs AFTER target expression is parsed)
        self.push_state(State::PiAfterBindings { loc, bindings });

        // Parse target expression (will push result to expr_stack)
        self.parse_expression(Precedence::Lowest);
    }

    /// Handle PiAfterBindings - build Pi node after target is parsed
    pub(super) fn handle_pi_after_bindings(
        &mut self,
        loc: Range<usize>,
        bindings: crate::syntax::TypedBindings,
    ) {
        // Pop the target from expr_stack
        let target = self.pop_expr();

        // Build the Pi node
        let end_loc = target.loc().end;
        let pi = Box::new(Expression::Pi(crate::syntax::Pi::new(
            loc.start..end_loc,
            bindings,
            target,
        )));

        // Push result - but go through ExprFinish to allow further precedence climbing
        // This is important for cases like: (Pi (x : A) -> B) -> C
        self.push_state(State::ExprFinish {
            partial: pi,
            min_prec: Precedence::Lowest,
        });
    }

    /// Parse typed bindings for Pi types
    /// Pi requires ALL bindings to be typed: Pi (x : A) (y : B) -> C
    /// Also supports implicit bindings: Pi {x : A} (y : B) -> C
    /// Unlike fun which allows untyped bindings: fun x y => e
    fn parse_pi_typed_bindings(&mut self) -> crate::syntax::TypedBindings {
        use crate::syntax::{Binder, Pattern, TypedBindingGroup};

        let mut groups = vec![];

        // Expect at least one typed binding group: (x : A) or {x : A}
        while self.at_token(Token::LParen) || self.at_token(Token::LBrace) {
            // Determine if this is explicit (x : A) or implicit {x : A}
            let is_implicit = self.at_token(Token::LBrace);
            let icit = if is_implicit {
                Icit::Implicit
            } else {
                Icit::Explicit
            };

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

        crate::syntax::TypedBindings::new(groups)
    }
}
