//! Namespace parsing handlers
//!
//! Implements the state machine pattern for namespace parsing.
//! Uses continuation-based states to keep the Rust call stack flat.

use crate::lex::Token;
use crate::parse::context::Context;
use crate::parse::state::State;
use crate::syntax::{Statement, Namespace, Id};
use std::ops::Range;

impl<'input> Context<'input> {
    /// Handle namespace start - sets up body parsing
    /// This handler does NOT loop - it queues states and returns immediately
    pub(super) fn handle_namespace_start(&mut self, loc: Range<usize>, name: Id) {
        // Enter block tracking
        self.enter_block(crate::parse::context::BlockKind::Namespace);
        
        // Expect opening brace
        if !self.at_token(Token::LBrace) {
            self.emit_error("Expected '{' after namespace name");
            self.exit_block();
            let stmt = self.make_error_statement("Invalid namespace");
            self.push_statement(stmt);
            return;
        }
        
        self.consume(Token::LBrace);

        // Track brace for error recovery
        self.push_brace(loc.clone());

        // Record current statement stack depth - all statements parsed
        // in the body will be added after this point
        let statement_stack_depth = self.statement_stack_len();

        // Push execution plan in REVERSE order (LIFO stack):
        // 1. First, push the END state (will run last)
        self.push_state(State::NamespaceEnd {
            loc: loc.clone(),
            name: name.clone(),
            statement_stack_depth,
        });
        
        // 2. Then push the BODY state (will run first)
        self.push_state(State::NamespaceBody {
            loc,
            name,
            statement_stack_depth,
        });
        
        // Return immediately - let the dispatcher handle the states
    }

    /// Handle namespace body - loops by re-queueing itself
    /// This implements the loop in the state machine, not in native recursion
    pub(super) fn handle_namespace_body(&mut self, loc: Range<usize>, name: Id, statement_stack_depth: usize) {
        // Check if we're done with the body
        if self.at_token(Token::RBrace) || self.at_end() {
            // Done parsing statements - exit and let NamespaceEnd handle cleanup
            return;
        }

        // Re-queue the loop state so it runs AGAIN after parsing the next statement
        self.push_state(State::NamespaceBody {
            loc: loc.clone(),
            name: name.clone(),
            statement_stack_depth,  // Pass through unchanged
        });
        
        // Queue the statement parser (will run before NamespaceBody runs again)
        self.push_state(State::Statement);
        
        // Return immediately - the dispatcher will:
        // 1. Pop and process State::Statement (pushes a statement to statement_stack)
        // 2. Pop and process State::NamespaceBody again (loops or exits)
    }

    /// Handle namespace end - collects statements and creates Namespace
    pub(super) fn handle_namespace_end(&mut self, loc: Range<usize>, name: Id, statement_stack_depth: usize) {
        // Expect closing brace
        if self.at_token(Token::RBrace) {
            self.consume(Token::RBrace);
            self.pop_brace();
        } else {
            self.emit_error("Expected '}' after namespace body");
        }
        
        // Exit block tracking
        self.exit_block();
        
        // Calculate how many statements were added to the stack
        let current_depth = self.statement_stack_len();
        let statement_count = current_depth - statement_stack_depth;
        
        // Pop all statements that were parsed in the body
        // They come off in LIFO order, so we need to reverse them
        let mut statements = Vec::with_capacity(statement_count);
        for _ in 0..statement_count {
            statements.push(self.pop_statement());
        }
        statements.reverse();  // Reverse to get original parse order
        
        // Create namespace statement
        let namespace = Namespace::new(loc, name, statements);
        self.push_statement(Statement::Namespace(namespace));
    }
}
