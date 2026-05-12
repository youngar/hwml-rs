//! Match expression parsing handlers
//!
//! Implements parsing for match expressions:
//! match <scrutinee> with | <pattern> => <expr> | ... end

use crate::lex::Token;
use crate::parse::context::Context;
use crate::parse::state::State;
use crate::syntax::{Expression, Match, MatchClause, Pattern};
use std::ops::Range;

impl<'input> Context<'input> {
    /// Handle match start - parse scrutinee
    pub(super) fn handle_match_start(&mut self, loc: Range<usize>) {
        // Push continuation (runs after scrutinee is parsed)
        self.push_state(State::MatchAfterScrutinee { loc });

        // Parse scrutinee expression
        self.parse_expression(crate::parse::state::Precedence::Lowest);
    }

    /// Handle after scrutinee - expect 'with' and start parsing clauses
    pub(super) fn handle_match_after_scrutinee(&mut self, loc: Range<usize>) {
        // Pop scrutinee from expr_stack
        let scrutinee = self.pop_expr();

        // Expect 'with' keyword
        if !self.at_token(Token::With) {
            self.emit_error("Expected 'with' after match scrutinee");
            let error_expr = Box::new(Expression::Error(
                crate::syntax::ExpressionError::new(loc, "Invalid match".to_string())
            ));
            self.push_expr(error_expr);
            return;
        }
        self.consume(Token::With);

        // Start parsing clauses
        self.push_state(State::MatchClauses {
            loc,
            scrutinee,
            clauses: vec![],
        });
    }

    /// Handle match clauses - loop parsing clauses until 'end'
    pub(super) fn handle_match_clauses(
        &mut self,
        loc: Range<usize>,
        scrutinee: Box<Expression>,
        mut clauses: Vec<MatchClause>,
    ) {
        // Check if we're done (at 'end' keyword)
        if self.at_token(Token::End) {
            self.consume(Token::End);

            // Create match expression and push to expr_stack
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
            // Skip to next clause or end
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
        if self.at_token(Token::Underscore) {
            let loc = self.current_location();
            self.consume(Token::Underscore);
            Pattern::Underscore(crate::syntax::Underscore::new(loc))
        } else if self.at_token(Token::Identifier) {
            let start_loc = self.current_location();
            let id = self.parse_id();
            let mut end_loc = id.loc.clone();

            // Check if followed by more identifiers (constructor application)
            let mut elements = vec![id.clone()];
            while self.at_token(Token::Identifier) && !self.at_token(Token::FatArrow) {
                let next_id = self.parse_id();
                end_loc = next_id.loc.clone();
                elements.push(next_id);
            }

            if elements.len() == 1 {
                Pattern::Id(id)
            } else {
                // Application pattern: Cons x xs
                use crate::syntax::AppSeq;
                let loc = start_loc.start..end_loc.end;
                Pattern::AppSeq(AppSeq::new(
                    loc,
                    elements.into_iter().map(Pattern::Id).collect()
                ))
            }
        } else if self.at_token(Token::Number) {
            let loc = self.current_location();
            let text = std::str::from_utf8(&self.input[loc.clone()])
                .unwrap_or("0")
                .to_string();
            self.advance();
            Pattern::Num(crate::syntax::Num::new(loc, text.into()))
        } else {
            // Error pattern
            self.emit_error("Expected pattern");
            let loc = self.current_location();
            Pattern::Error(crate::syntax::PatternError::new(loc, "Invalid pattern".to_string()))
        }
    }
}
