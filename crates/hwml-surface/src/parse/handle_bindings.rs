//! Async binding parsing handlers
//!
//! Implements the async/continuation-based parsing of bindings to avoid recursion.
//! Bindings can contain arbitrary type expressions (which themselves can be complex),
//! so we use the async expression parser and state machine.

use crate::lex::Token;
use crate::parse::context::Context;
use crate::parse::state::{Precedence, State};
use crate::syntax::{Binder, BindingGroup, Bindings, Pattern, TypedBindingGroup, UntypedBindingGroup};
use hwml_core::common::Icit;

impl Context<'_> {
    /// Start parsing bindings - called from places that need bindings
    /// Pushes result to bindings_stack when done
    pub(super) fn parse_bindings_async(&mut self, continuation: State) {
        // Push the continuation first (runs LAST)
        self.push_state(continuation);
        
        // Push the binding parser (runs FIRST)
        self.push_state(State::ParseBindingsStart {
            groups: vec![],
        });
    }
    
    /// Handle ParseBindingsStart - accumulate binding groups
    pub(super) fn handle_parse_bindings_start(&mut self, mut groups: Vec<BindingGroup>) {
        // Check if we have more bindings to parse
        // Bindings start with '(' for explicit, '{' for implicit, bare identifier, or underscore
        if self.at_token(Token::LParen) || self.at_token(Token::LBrace) {
            // Determine if this is an implicit binding group
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

            // Check if this is a typed binding group (has : Type)
            if self.at_token(Token::Colon) {
                self.consume(Token::Colon);

                // Push continuation (runs AFTER type expression is parsed)
                self.push_state(State::BindingGroupAfterType {
                    binders,
                    groups,
                    icit,
                    is_implicit,
                    continuation: Box::new(State::ParseBindingsStart { groups: vec![] }), // dummy, will be replaced
                });

                // Parse type expression asynchronously (runs FIRST)
                // This allows complex types like Pi, match expressions, etc.
                self.parse_expression(Precedence::Lowest);
            } else {
                // Untyped binding group
                let closing_token = if is_implicit { Token::RBrace } else { Token::RParen };
                let closing_str = if is_implicit { "'}'" } else { "')'" };

                if !self.at_token(closing_token) {
                    self.emit_error(&format!("Expected {} or ':' after binders", closing_str));
                } else {
                    self.consume(closing_token);
                }

                groups.push(BindingGroup::Untyped(UntypedBindingGroup::new(binders)));

                // Continue parsing more binding groups
                self.push_state(State::ParseBindingsStart { groups });
            }
        } else if self.at_token(Token::Identifier) &&
                  !self.at_token(Token::Colon) &&
                  !self.at_token(Token::ColonEqual) {
            // Bare identifier (untyped)
            let id = self.parse_id();
            let loc = id.loc.clone();
            let binder = Binder::new(loc, Pattern::Id(id));
            groups.push(BindingGroup::Untyped(UntypedBindingGroup::new(vec![binder])));
            
            // Continue parsing more binding groups
            self.push_state(State::ParseBindingsStart { groups });
        } else if self.at_token(Token::Underscore) {
            // Bare underscore (untyped)
            let loc = self.current_location();
            self.consume(Token::Underscore);
            let binder = Binder::new(
                loc.clone(),
                Pattern::Underscore(crate::syntax::Underscore::new(loc)),
            );
            groups.push(BindingGroup::Untyped(UntypedBindingGroup::new(vec![binder])));
            
            // Continue parsing more binding groups
            self.push_state(State::ParseBindingsStart { groups });
        } else {
            // No more bindings - push result to bindings_stack
            self.push_bindings(Bindings::new(groups));
        }
    }
    
    /// Handle after parsing type in a binding group
    pub(super) fn handle_binding_group_after_type(
        &mut self,
        binders: Vec<Binder>,
        mut groups: Vec<BindingGroup>,
        icit: Icit,
        is_implicit: bool,
    ) {
        // Pop the type expression from expr_stack
        let ty = self.pop_expr();

        // Expect closing delimiter matching the opening
        let closing_token = if is_implicit { Token::RBrace } else { Token::RParen };
        let closing_str = if is_implicit { "'}'" } else { "')'" };

        if !self.at_token(closing_token) {
            self.emit_error(&format!("Expected {} after typed binding", closing_str));
        } else {
            self.consume(closing_token);
        }

        // Add this typed binding group with the correct icit
        groups.push(BindingGroup::Typed(TypedBindingGroup::new(binders, ty, icit)));

        // Continue parsing more binding groups
        self.push_state(State::ParseBindingsStart { groups });
    }

    /// Parse telescope bindings for dependent arrows: (a : A) (b : B) -> C
    /// Only typed bindings in parentheses are valid
    /// DEPRECATED: This will be removed in favor of parse-then-reinterpret
    pub(super) fn handle_parse_telescope_bindings(
        &mut self,
        mut groups: Vec<crate::syntax::TypedBindingGroup>,
    ) {
        // TEMPORARILY DISABLED - will be replaced with parse-then-reinterpret
        // Check if we have another telescope binding: ( Identifier :
        if false && self.at_token(Token::LParen) {
            self.consume(Token::LParen);

            // Parse binders
            let mut binders = vec![];
            while self.at_token(Token::Identifier) || self.at_token(Token::Underscore) {
                if self.at_token(Token::Identifier) {
                    let id = self.parse_id();
                    let loc = id.loc.clone();
                    binders.push(Binder::new(loc, Pattern::Id(id)));
                } else {
                    let loc = self.current_location();
                    self.consume(Token::Underscore);
                    binders.push(Binder::new(
                        loc.clone(),
                        Pattern::Underscore(crate::syntax::Underscore::new(loc)),
                    ));
                }
            }

            // Expect ':'
            if !self.at_token(Token::Colon) {
                self.emit_error("Expected ':' in telescope binding");
                // Push empty typed bindings and return
                self.push_typed_bindings(crate::syntax::TypedBindings::new(groups));
                return;
            }
            self.consume(Token::Colon);

            // Push continuation (runs AFTER type is parsed)
            self.push_state(State::TelescopeBindingAfterType {
                binders,
                groups,
            });

            // Parse type expression asynchronously
            self.parse_expression(crate::parse::state::Precedence::Lowest);
        } else {
            // No more telescope bindings - push accumulated groups to typed_bindings_stack
            self.push_typed_bindings(crate::syntax::TypedBindings::new(groups));
        }
    }

    /// Handle after parsing type in a telescope binding
    pub(super) fn handle_telescope_binding_after_type(
        &mut self,
        binders: Vec<Binder>,
        mut groups: Vec<crate::syntax::TypedBindingGroup>,
    ) {
        // Pop type from expr_stack
        let ty = self.pop_expr();

        // Expect ')'
        if !self.at_token(Token::RParen) {
            self.emit_error("Expected ')' after telescope binding");
        } else {
            self.consume(Token::RParen);
        }

        // Add this group
        groups.push(crate::syntax::TypedBindingGroup::new(binders, ty, Icit::Explicit));

        // Continue parsing more telescope bindings
        self.push_state(State::ParseTelescopeBindings { groups });
    }
}
