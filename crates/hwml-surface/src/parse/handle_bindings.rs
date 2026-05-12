//! Async binding parsing handlers
//!
//! Implements the async/continuation-based parsing of bindings to avoid recursion.
//! Bindings can contain arbitrary type expressions (which themselves can be complex),
//! so we use the async expression parser and state machine.

use crate::lex::Token;
use crate::parse::context::Context;
use crate::parse::state::{Precedence, State};
use crate::syntax::{Binder, BindingGroup, Bindings, Pattern, TypedBindingGroup, UntypedBindingGroup};

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
        // Bindings start with '(', bare identifier, or underscore
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
                    continuation: Box::new(State::ParseBindingsStart { groups: vec![] }), // dummy, will be replaced
                });
                
                // Parse type expression asynchronously (runs FIRST)
                // This allows complex types like Pi, match expressions, etc.
                self.parse_expression(Precedence::Lowest);
            } else {
                // Untyped binding group
                if !self.at_token(Token::RParen) {
                    self.emit_error("Expected ')' or ':' after binders");
                } else {
                    self.consume(Token::RParen);
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
    ) {
        // Pop the type expression from expr_stack
        let ty = self.pop_expr();
        
        // Expect ')'
        if !self.at_token(Token::RParen) {
            self.emit_error("Expected ')' after typed binding");
        } else {
            self.consume(Token::RParen);
        }
        
        // Add this typed binding group
        groups.push(BindingGroup::Typed(TypedBindingGroup::new(binders, ty)));
        
        // Continue parsing more binding groups
        self.push_state(State::ParseBindingsStart { groups });
    }
}
