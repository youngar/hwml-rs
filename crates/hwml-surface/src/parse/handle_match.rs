//! Match expression parsing handlers
//!
//! Implements parsing for match expressions:
//! <scrutinee> match { | <pattern> => <expr> | ... }

use crate::lex::Token;
use crate::parse::context::Context;
use crate::parse::state::State;
use crate::syntax::{Expression, Match, MatchClause, Pattern};
use std::ops::Range;

impl<'input> Context<'input> {
    /// Handle match clauses - loop parsing clauses until '}'
    pub(super) fn handle_match_clauses(
        &mut self,
        loc: Range<usize>,
        scrutinee: Box<Expression>,
        mut clauses: Vec<MatchClause>,
    ) {
        // Check if we're done (at '}' closing brace)
        if self.at_token(Token::RBrace) {
            self.consume(Token::RBrace);

            // Create match expression and push to expr_stack
            let match_expr = Box::new(Expression::Match(Match::new(scrutinee, clauses)));
            self.push_expr(match_expr);
            return;
        }

        // Check for EOF or unexpected tokens (error recovery)
        if self.at_end() || self.at_sync_point() {
            self.emit_error("Expected '}' to close match expression");
            // Create partial match with clauses we have so far
            let match_expr = Box::new(Expression::Match(Match::new(scrutinee, clauses)));
            self.push_expr(match_expr);
            return;
        }

        // Parse next clause: | <pattern> => <expr>

        // Optional '|' before clause (first clause may omit it)
        if self.at_token(Token::Pipe) {
            self.consume(Token::Pipe);
        } else if !clauses.is_empty() {
            self.emit_error("Expected '|' before match clause");
        }

        // Parse pattern
        let pattern = self.parse_pattern();

        // Expect '=>'
        if !self.at_token(Token::FatArrow) {
            self.emit_error("Expected '=>' after match pattern");

            // Smart recovery: skip to next pattern boundary (pipe or closing brace)
            // This uses pattern-level sync points for better recovery
            self.skip_to_pattern_boundary();

            // If we found a pipe, continue parsing more clauses
            // If we found a closing brace, finish the match
            if self.at_token(Token::RBrace) || self.at_end() {
                let match_expr = Box::new(Expression::Match(Match::new(scrutinee, clauses)));
                self.push_expr(match_expr);
                return;
            }

            // Otherwise, loop back to parse next clause
            // (we're probably at a pipe now)
            self.push_state(State::MatchClauses {
                loc,
                scrutinee,
                clauses,
            });
            return;
        }
        self.consume(Token::FatArrow);

        // Now we need to parse the body expression
        // This is async, so we need a continuation state

        // We'll use a new state to collect the body after it's parsed
        self.push_state(State::MatchClauseAfterBody {
            loc: loc.clone(),
            scrutinee: scrutinee.clone(),
            clauses,
            pattern,
        });

        // Parse body expression
        self.parse_expression(crate::parse::state::Precedence::Lowest);
    }

    /// Handle after parsing clause body - add clause and loop back
    pub(super) fn handle_match_clause_after_body(
        &mut self,
        loc: Range<usize>,
        scrutinee: Box<Expression>,
        mut clauses: Vec<MatchClause>,
        pattern: Pattern,
    ) {
        // Pop body from expr_stack
        let body = self.pop_expr();

        // Create clause
        let clause = MatchClause::new(pattern, body);
        clauses.push(clause);

        // Loop back to parse more clauses
        self.push_state(State::MatchClauses {
            loc,
            scrutinee,
            clauses,
        });
    }

    /// Parse a pattern - simple version for now
    fn parse_pattern(&mut self) -> Pattern {
        // Check if we're at EOF or a sync point before trying to parse
        if self.at_end() || self.at_pattern_sync_point() {
            self.emit_error("Expected pattern");
            let loc = self.current_location();
            return Pattern::Error(crate::syntax::PatternError::new(
                loc,
                "Missing pattern".to_string(),
            ));
        }

        if self.at_token(Token::Underscore) {
            let loc = self.current_location();
            self.consume(Token::Underscore);
            Pattern::Underscore(crate::syntax::Underscore::new(loc))
        } else if self.at_token(Token::Identifier) {
            let start_loc = self.current_location();
            let id = self.parse_id();
            let mut end_loc = id.loc.clone();

            // Check if followed by more patterns (constructor application)
            // e.g., `Cons x xs` or `Just _` or `succ _`
            let mut elements = vec![Pattern::Id(id)];
            while (self.at_token(Token::Identifier) || self.at_token(Token::Underscore))
                && !self.at_pattern_sync_point()
            {
                let pattern = if self.at_token(Token::Underscore) {
                    let loc = self.current_location();
                    self.consume(Token::Underscore);
                    end_loc = loc.clone();
                    Pattern::Underscore(crate::syntax::Underscore::new(loc))
                } else {
                    let next_id = self.parse_id();
                    end_loc = next_id.loc.clone();
                    Pattern::Id(next_id)
                };
                elements.push(pattern);
            }

            if elements.len() == 1 {
                // Just a single identifier
                if let Pattern::Id(id) = elements.into_iter().next().unwrap() {
                    Pattern::Id(id)
                } else {
                    unreachable!()
                }
            } else {
                // Application pattern: Cons x xs, or Just _, or succ _
                use crate::syntax::AppSeq;
                let loc = start_loc.start..end_loc.end;
                Pattern::AppSeq(AppSeq::new(loc, elements))
            }
        } else if self.at_token(Token::Number) {
            let loc = self.current_location();
            let text = std::str::from_utf8(&self.input[loc.clone()])
                .unwrap_or("0")
                .to_string();
            self.advance();
            Pattern::Num(crate::syntax::Num::new(loc, text.into()))
        } else {
            // Error pattern - emit error and skip to pattern boundary
            self.emit_error("Expected pattern (identifier, underscore, or number)");
            let loc = self.current_location();

            // Skip to next safe point
            self.skip_to_pattern_boundary();

            Pattern::Error(crate::syntax::PatternError::new(
                loc,
                "Invalid pattern".to_string(),
            ))
        }
    }
}
