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
        // Parse bindings asynchronously - they'll be pushed to bindings_stack
        let continuation = State::DefAfterBindings {
            loc,
            name,
            bindings: crate::syntax::Bindings::new(vec![]), // dummy, will pop from stack
        };
        self.parse_bindings_async(continuation);
    }

    pub(super) fn handle_def_after_bindings(&mut self, loc: Range<usize>, name: Id, _bindings: Bindings) {
        // Pop the ACTUAL bindings from bindings_stack (ignore dummy passed in state)
        let bindings = self.pop_bindings();
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
        self.push_state(State::MetaAfterBindings { loc, name, bindings });
    }

    pub(super) fn handle_meta_after_bindings(&mut self, loc: Range<usize>, name: Id, bindings: Bindings) {
        if self.at_token(Token::Colon) {
            self.consume(Token::Colon);

            // Push continuation (will pop type from expr_stack)
            let dummy_ty = Box::new(Expression::Hole(crate::syntax::ExpressionHole::new(0..0, None)));
            self.push_state(State::MetaAfterType {
                loc,
                name,
                bindings,
                ty: dummy_ty // Ignored - handler will pop from stack
            });

            // Push expression parser (runs first)
            self.parse_expression(crate::parse::state::Precedence::Lowest);
        } else if self.at_token(Token::ColonEqual) {
            self.consume(Token::ColonEqual);

            // Push continuation
            self.push_state(State::MetaAfterValue {
                loc,
                name,
                bindings,
                ty: None,
            });

            // Push expression parser
            self.parse_expression(crate::parse::state::Precedence::Lowest);
        } else {
            self.emit_error("Expected ':' or ':=' after meta bindings");
            let stmt = self.make_error_statement("Invalid meta");
            self.push_statement(stmt);
        }
    }

    pub(super) fn handle_meta_after_type(&mut self, loc: Range<usize>, name: Id, bindings: Bindings, _ty: Box<Expression>) {
        // Pop the ACTUAL type from the expression stack
        let ty = self.pop_expr();

        if self.at_token(Token::ColonEqual) {
            self.consume(Token::ColonEqual);

            // Push continuation
            self.push_state(State::MetaAfterValue {
                loc,
                name,
                bindings,
                ty: Some(ty),
            });

            // Push expression parser
            self.parse_expression(crate::parse::state::Precedence::Lowest);
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

            // Push continuation FIRST (will pop type from expr_stack)
            self.push_state(State::PrimAfterType { loc, name });

            // Push expression parser SECOND (runs first)
            self.parse_expression(crate::parse::state::Precedence::Lowest);
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
        use crate::syntax::OpenModifier;

        let namespace = self.pop_id();
        let mut modifiers = vec![];
        let mut as_alias = None;

        // Parse optional modifiers
        loop {
            if self.at_token(Token::Hiding) {
                self.consume(Token::Hiding);
                // Parse (id1, id2, ...)
                if self.at_token(Token::LParen) {
                    self.consume(Token::LParen);
                    let mut names = vec![];
                    while self.at_token(Token::Identifier) {
                        names.push(self.parse_id());
                        if self.at_token(Token::Comma) {
                            self.consume(Token::Comma);
                        }
                    }
                    if self.at_token(Token::RParen) {
                        self.consume(Token::RParen);
                    }
                    modifiers.push(OpenModifier::Hiding(loc.clone(), names));
                }
            } else if self.at_token(Token::Only) {
                self.consume(Token::Only);
                // Parse (id1, id2, ...)
                if self.at_token(Token::LParen) {
                    self.consume(Token::LParen);
                    let mut names = vec![];
                    while self.at_token(Token::Identifier) {
                        names.push(self.parse_id());
                        if self.at_token(Token::Comma) {
                            self.consume(Token::Comma);
                        }
                    }
                    if self.at_token(Token::RParen) {
                        self.consume(Token::RParen);
                    }
                    modifiers.push(OpenModifier::Only(loc.clone(), names));
                }
            } else if self.at_token(Token::Renaming) {
                self.consume(Token::Renaming);
                // Parse (from to)
                if self.at_token(Token::LParen) {
                    self.consume(Token::LParen);
                    if self.at_token(Token::Identifier) {
                        let from = self.parse_id();
                        if self.at_token(Token::Identifier) {
                            let to = self.parse_id();
                            modifiers.push(OpenModifier::Renaming(loc.clone(), from, to));
                        }
                    }
                    if self.at_token(Token::RParen) {
                        self.consume(Token::RParen);
                    }
                }
            } else {
                break;
            }
        }

        let open = Open::new(loc, namespace, modifiers, as_alias);
        self.push_statement(Statement::Open(open));
    }
}
