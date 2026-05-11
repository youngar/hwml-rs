//! Statement parsing handlers
//!
//! This module implements the state handlers for parsing statements:
//! - def (definitions)
//! - meta (meta definitions)
//! - prim (primitive declarations)
//! - namespace
//! - open
//! - inductive

use crate::lex::Token;
use crate::parse::context::Context;
use crate::parse::state::State;
use crate::syntax::{Statement, Def, Meta, Prim, Id, Bindings, Expression, Open};
use std::ops::Range;

impl<'input> Context<'input> {
    /// Handle Statement state - dispatch based on keyword
    pub(super) fn handle_statement(&mut self) {
        if self.at_end() {
            return;
        }

        let loc = self.current_location();

        match self.peek() {
            Some(Token::Def) => {
                self.consume(Token::Def);
                self.push_state(State::DefStart { loc });
            }
            Some(Token::Meta) => {
                self.consume(Token::Meta);
                self.push_state(State::MetaStart { loc });
            }
            Some(Token::Prim) => {
                self.consume(Token::Prim);
                self.push_state(State::PrimStart { loc });
            }
            Some(Token::Namespace) => {
                self.consume(Token::Namespace);
                if self.at_token(Token::Identifier) {
                    let name = self.parse_id();
                    self.push_state(State::NamespaceStart { loc, name });
                } else {
                    self.emit_error("Expected identifier after 'namespace'");
                    let stmt = self.make_error_statement("Invalid namespace");
                    self.push_statement(stmt);
                }
            }
            Some(Token::Open) => {
                self.consume(Token::Open);
                if self.at_token(Token::Identifier) {
                    let namespace = self.parse_id();
                    self.push_id(namespace);
                    self.push_state(State::OpenStart { loc });
                } else {
                    self.emit_error("Expected identifier after 'open'");
                    let stmt = self.make_error_statement("Invalid open");
                    self.push_statement(stmt);
                }
            }
            Some(Token::Inductive) => {
                self.consume(Token::Inductive);
                self.push_state(State::InductiveStart { loc });
            }
            Some(_) => {
                self.emit_error(format!("Unexpected token: {:?}", self.peek()));
                self.skip_to_statement_boundary();
                let stmt = self.make_error_statement("Invalid statement");
                self.push_statement(stmt);
            }
            None => {}
        }
    }

    /// Helper: Skip to next statement boundary (for error recovery)
    pub(super) fn skip_to_statement_boundary(&mut self) {
        while !self.at_end() {
            match self.peek() {
                Some(Token::Def) | Some(Token::Meta) | Some(Token::Prim)
                | Some(Token::Namespace) | Some(Token::Open) | Some(Token::Inductive) => break,
                _ => self.advance(),
            }
        }
    }

    // ===== Def Statement Handlers =====

    pub(super) fn handle_def_start(&mut self, loc: Range<usize>) {
        if self.at_token(Token::Identifier) {
            let name = self.parse_id();
            self.push_state(State::DefAfterName { loc, name });
        } else {
            self.emit_error("Expected identifier after 'def'");
            let stmt = self.make_error_statement("Invalid def");
            self.push_statement(stmt);
        }
    }

    pub(super) fn handle_def_after_name(&mut self, loc: Range<usize>, name: Id) {
        let bindings = self.parse_bindings();
        self.push_state(State::DefAfterBindings { loc, name, bindings });
    }

    pub(super) fn handle_def_after_bindings(&mut self, loc: Range<usize>, name: Id, bindings: Bindings) {
        if self.at_token(Token::Colon) {
            self.consume(Token::Colon);

            // Push TWO states: continuation first, then expression parser
            // When expression finishes, it will push result to expr_stack
            // Then DefAfterType will pop it
            let dummy_ty = Box::new(Expression::Hole(crate::syntax::ExpressionHole::new(0..0, None)));
            self.push_state(State::DefAfterType {
                loc,
                name,
                bindings,
                ty: dummy_ty // Will be ignored - handler will pop from stack
            });

            // Push expression parser (runs first)
            self.parse_expression(crate::parse::state::Precedence::Lowest);
        } else if self.at_token(Token::ColonEqual) {
            self.consume(Token::ColonEqual);

            // Push continuation
            self.push_state(State::DefAfterValue {
                loc,
                name,
                bindings,
                ty: None,
            });

            // Push expression parser
            self.parse_expression(crate::parse::state::Precedence::Lowest);
        } else {
            self.emit_error("Expected ':' or ':=' after def bindings");
            let stmt = self.make_error_statement("Invalid def");
            self.push_statement(stmt);
        }
    }

    pub(super) fn handle_def_after_type(&mut self, loc: Range<usize>, name: Id, bindings: Bindings, _ty: Box<Expression>) {
        // Pop the ACTUAL type from the expression stack (ignore the dummy passed in state)
        let ty = self.pop_expr();

        if self.at_token(Token::ColonEqual) {
            self.consume(Token::ColonEqual);

            // Push continuation state (will run after expression is parsed)
            self.push_state(State::DefAfterValue {
                loc,
                name,
                bindings,
                ty: Some(ty),
            });

            // Push expression parsing state (will run first)
            self.parse_expression(crate::parse::state::Precedence::Lowest);
        } else {
            self.emit_error("Expected ':=' after def type");
            let stmt = self.make_error_statement("Invalid def");
            self.push_statement(stmt);
        }
    }

    pub(super) fn handle_def_after_value(&mut self, loc: Range<usize>, name: Id, bindings: Bindings, ty: Option<Box<Expression>>) {
        let value = self.pop_expr();
        let def = Def::new(loc, name, bindings, ty, value);
        self.push_statement(Statement::Def(def));
    }

    // ===== Meta Statement Handlers =====

    pub(super) fn handle_meta_start(&mut self, loc: Range<usize>) {
        if self.at_token(Token::Identifier) {
            let name = self.parse_id();
            self.push_state(State::MetaAfterName { loc, name });
        } else {
            self.emit_error("Expected identifier after 'meta'");
            let stmt = self.make_error_statement("Invalid meta");
            self.push_statement(stmt);
        }
    }

    pub(super) fn handle_meta_after_name(&mut self, loc: Range<usize>, name: Id) {
        let bindings = self.parse_bindings();

        let ty = if self.at_token(Token::Colon) {
            self.consume(Token::Colon);
            self.parse_expression(crate::parse::state::Precedence::Lowest);
            Some(self.pop_expr())
        } else {
            None
        };

        if self.at_token(Token::ColonEqual) {
            self.consume(Token::ColonEqual);
            self.parse_expression(crate::parse::state::Precedence::Lowest);
            let value = self.pop_expr();
            let meta = Meta::new(loc, name, bindings, ty, value);
            self.push_statement(Statement::Meta(meta));
        } else {
            self.emit_error("Expected ':=' after meta signature");
            let stmt = self.make_error_statement("Invalid meta");
            self.push_statement(stmt);
        }
    }

    pub(super) fn handle_meta_after_bindings(&mut self, loc: Range<usize>, name: Id, bindings: Bindings) {
        if self.at_token(Token::Colon) {
            self.consume(Token::Colon);
            self.parse_expression(crate::parse::state::Precedence::Lowest);
            let ty = self.pop_expr();
            self.push_state(State::MetaAfterType { loc, name, bindings, ty });
        } else if self.at_token(Token::ColonEqual) {
            self.consume(Token::ColonEqual);
            self.parse_expression(crate::parse::state::Precedence::Lowest);
            let value = self.pop_expr();
            let meta = Meta::new(loc, name, bindings, None, value);
            self.push_statement(Statement::Meta(meta));
        } else {
            self.emit_error("Expected ':' or ':=' after meta bindings");
            let stmt = self.make_error_statement("Invalid meta");
            self.push_statement(stmt);
        }
    }

    pub(super) fn handle_meta_after_type(&mut self, loc: Range<usize>, name: Id, bindings: Bindings, ty: Box<Expression>) {
        if self.at_token(Token::ColonEqual) {
            self.consume(Token::ColonEqual);
            self.parse_expression(crate::parse::state::Precedence::Lowest);
            let value = self.pop_expr();
            let meta = Meta::new(loc, name, bindings, Some(ty), value);
            self.push_statement(Statement::Meta(meta));
        } else {
            self.emit_error("Expected ':=' after meta type");
            let stmt = self.make_error_statement("Invalid meta");
            self.push_statement(stmt);
        }
    }

    pub(super) fn handle_meta_after_value(&mut self, loc: Range<usize>, name: Id, bindings: Bindings, ty: Option<Box<Expression>>) {
        let value = self.pop_expr();
        let meta = Meta::new(loc, name, bindings, ty, value);
        self.push_statement(Statement::Meta(meta));
    }

    // ===== Prim Statement Handlers =====

    pub(super) fn handle_prim_start(&mut self, loc: Range<usize>) {
        if self.at_token(Token::Identifier) {
            let name = self.parse_id();
            self.push_state(State::PrimAfterName { loc, name });
        } else {
            self.emit_error("Expected identifier after 'prim'");
            let stmt = self.make_error_statement("Invalid prim");
            self.push_statement(stmt);
        }
    }

    pub(super) fn handle_prim_after_name(&mut self, loc: Range<usize>, name: Id) {
        if self.at_token(Token::Colon) {
            self.consume(Token::Colon);
            self.parse_expression(crate::parse::state::Precedence::Lowest);
            self.push_state(State::PrimAfterType { loc, name });
        } else {
            self.emit_error("Expected ':' after prim name");
            let stmt = self.make_error_statement("Invalid prim");
            self.push_statement(stmt);
        }
    }

    pub(super) fn handle_prim_after_type(&mut self, loc: Range<usize>, name: Id) {
        let ty = self.pop_expr();
        let prim = Prim::new(loc, name, ty);
        self.push_statement(Statement::Prim(prim));
    }

    // ===== Open Statement Handler =====

    pub(super) fn handle_open_start(&mut self, loc: Range<usize>) {
        let namespace = self.pop_id();
        // No modifiers or aliases for now
        let open = Open::new(loc, namespace, vec![], None);
        self.push_statement(Statement::Open(open));
    }
}
