//! Top-down recursive descent parser
//!
//! Replaces LALRPOP with a hand-written parser for better error recovery,
//! error messages, and control over parsing.

pub mod provenance;
pub mod state;
pub mod context;
mod handle_stmt;
mod handle_expr;
mod handle_pattern;
mod handle_inductive;
mod handle_namespace;
mod handle_recovery;
mod handle_match;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod test_statements;

#[cfg(test)]
mod test_expressions;

#[cfg(test)]
mod test_patterns;

#[cfg(test)]
mod test_inductive;

#[cfg(test)]
mod test_namespace;

#[cfg(test)]
mod test_recovery;

#[cfg(test)]
mod test_match;

use crate::lex::Lexer;
use context::{Context, ParseResult};
use state::State;

/// Top-down parser
pub struct Parser<'input> {
    context: Context<'input>,
}

impl<'input> Parser<'input> {
    /// Create a new parser from input
    pub fn new(input: &'input [u8]) -> Self {
        // Lex the input
        let lexer = Lexer::new(input);

        // Convert (start, Token, end) to (Token, Range<usize>)
        // Filter out trivia (whitespace, comments)
        let tokens: Vec<_> = lexer
            .filter(|(_, tok, _)| !tok.is_trivia())
            .map(|(start, tok, end)| (tok, start..end))
            .collect();

        let context = Context::new(input, tokens);

        Self { context }
    }
    
    /// Parse the input into a Program
    pub fn parse(mut self) -> ParseResult {
        // Parse statements until EOF
        while !self.context.at_end() {
            // Track error count before parsing statement
            let error_count_before = self.context.error_count();

            self.context.push_state(State::Statement);

            // Process all states on the stack until empty
            while let Some(state) = self.context.pop_state() {
                self.handle_state(state);
            }

            // Check if we made progress
            let error_count_after = self.context.error_count();

            // If we added errors and haven't advanced, try to recover
            if error_count_after > error_count_before && !self.context.at_end() {
                // Check if we're stuck at the same position
                if !self.context.at_sync_point() {
                    // Skip to next statement boundary
                    self.context.skip_to_statement_boundary();
                }
            }
        }

        // Finalize and return result
        self.context.finalize()
    }
    
    /// Dispatch to appropriate handler based on state
    fn handle_state(&mut self, state: State) {
        match state {
            State::Program => {
                // Program state not used - we handle this in the main parse() loop
            }
            State::Statement => self.context.handle_statement(),

            // Def
            State::DefStart { loc } => self.context.handle_def_start(loc),
            State::DefAfterName { loc, name } => {
                self.context.handle_def_after_name(loc, name)
            }
            State::DefAfterBindings { loc, name, bindings } => {
                self.context.handle_def_after_bindings(loc, name, bindings)
            }
            State::DefAfterType { loc, name, bindings, ty } => {
                self.context.handle_def_after_type(loc, name, bindings, ty)
            }
            State::DefAfterValue { loc, name, bindings, ty } => {
                self.context.handle_def_after_value(loc, name, bindings, ty)
            }

            // Meta (similar to def)
            State::MetaStart { loc } => self.context.handle_meta_start(loc),
            State::MetaAfterName { loc, name } => {
                self.context.handle_meta_after_name(loc, name)
            }
            State::MetaAfterBindings { loc, name, bindings } => {
                self.context.handle_meta_after_bindings(loc, name, bindings)
            }
            State::MetaAfterType { loc, name, bindings, ty } => {
                self.context.handle_meta_after_type(loc, name, bindings, ty)
            }
            State::MetaAfterValue { loc, name, bindings, ty } => {
                self.context.handle_meta_after_value(loc, name, bindings, ty)
            }

            // Prim
            State::PrimStart { loc } => self.context.handle_prim_start(loc),
            State::PrimAfterName { loc, name } => {
                self.context.handle_prim_after_name(loc, name)
            }
            State::PrimAfterType { loc, name } => {
                self.context.handle_prim_after_type(loc, name)
            }

            // Inductive
            State::InductiveStart { loc } => {
                self.context.handle_inductive_start(loc)
            }

            // Other inductive states not used (we handle everything in InductiveStart)
            State::InductiveAfterName { .. } |
            State::InductiveAfterParams { .. } |
            State::InductiveAfterIndices { .. } |
            State::InductiveConstructors { .. } |
            State::Constructor { .. } => {
                // These states exist but we don't use them in the current implementation
                self.context.emit_error("Unexpected inductive state");
            }

            // Namespace
            State::NamespaceStart { loc, name } => {
                self.context.handle_namespace_start(loc, name)
            }
            State::NamespaceBody { loc, name, statement_stack_depth } => {
                self.context.handle_namespace_body(loc, name, statement_stack_depth)
            }
            State::NamespaceEnd { loc, name, statement_stack_depth } => {
                self.context.handle_namespace_end(loc, name, statement_stack_depth)
            }

            // Open
            State::OpenStart { loc } => {
                self.context.handle_open_start(loc)
            }

            // TODO: Add remaining states (match, etc.)
            _ => {
                self.context.emit_error(format!("Unimplemented state: {:?}", state));
            }
        }
    }
}
