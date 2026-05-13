//! Error recovery handlers
//!
//! This module implements bracket-aware and context-aware error recovery.
//! Inspired by Carbon's error recovery strategies.

use crate::lex::Token;
use crate::parse::context::Context;

impl<'input> Context<'input> {
    /// Skip to the matching closing brace using brace_stack depth tracking.
    ///
    /// This is smarter than token-by-token skipping because it handles nested braces correctly.
    /// Returns true if we found and consumed the matching brace, false if we hit EOF.
    ///
    /// # Strategy
    /// - Track brace depth starting from current depth
    /// - Increment on LBrace, decrement on RBrace
    /// - Stop when we reach the matching closing brace (depth returns to starting level)
    /// - Stop at EOF if we never find the match
    pub(super) fn skip_to_matching_brace(&mut self) -> bool {
        let target_depth = self.brace_depth();

        while !self.at_end() {
            match self.peek() {
                Some(Token::RBrace) => {
                    // Check if this closes our target brace
                    if self.brace_depth() == target_depth {
                        // This is the matching brace - consume it and return
                        self.consume(Token::RBrace);
                        return true;
                    } else if self.brace_depth() > target_depth {
                        // This closes an inner brace
                        self.consume(Token::RBrace);
                        self.pop_brace();
                    } else {
                        // We've already gone past our target depth - stop without consuming
                        return false;
                    }
                }
                Some(Token::LBrace) => {
                    let loc = self.consume(Token::LBrace);
                    self.push_brace(loc);
                }
                _ => {
                    self.advance();
                }
            }
        }

        // Hit EOF without finding matching brace
        false
    }

    /// Skip to the matching closing paren using paren_stack depth tracking.
    ///
    /// Similar to skip_to_matching_brace but for parentheses.
    /// Returns true if we found and consumed the matching paren, false if we hit EOF.
    pub(super) fn skip_to_matching_paren(&mut self) -> bool {
        let target_depth = self.paren_depth();

        while !self.at_end() {
            match self.peek() {
                Some(Token::RParen) => {
                    // Check if this closes our target paren
                    if self.paren_depth() == target_depth {
                        // This is the matching paren - consume it and return
                        self.consume(Token::RParen);
                        return true;
                    } else if self.paren_depth() > target_depth {
                        // This closes an inner paren
                        self.consume(Token::RParen);
                        self.pop_paren();
                    } else {
                        // We've already gone past our target depth - stop without consuming
                        return false;
                    }
                }
                Some(Token::LParen) => {
                    let loc = self.consume(Token::LParen);
                    self.push_paren(loc);
                }
                _ => {
                    self.advance();
                }
            }
        }

        // Hit EOF without finding matching paren
        false
    }

    /// Skip an entire bracketed region when we can't parse its contents.
    ///
    /// This is used when we encounter an error inside braces or parens and want to
    /// skip to the end of that region to continue parsing.
    ///
    /// # Strategy
    /// - If we're inside braces, skip to matching RBrace
    /// - If we're inside parens, skip to matching RParen
    /// - Otherwise, skip to next statement boundary
    pub(super) fn skip_bracketed_region(&mut self) {
        // Try to skip based on current bracket context
        if self.brace_depth() > 0 {
            // We're inside braces - skip to matching close
            self.skip_to_matching_brace();
        } else if self.paren_depth() > 0 {
            // We're inside parens - skip to matching close
            self.skip_to_matching_paren();
        } else {
            // Not inside brackets - skip to statement boundary
            self.skip_to_statement_boundary();
        }
    }

    /// Enhanced statement boundary skip with bracket awareness.
    ///
    /// This is smarter than the basic skip_to_statement_boundary because it:
    /// - Doesn't skip past closing braces that belong to parent blocks
    /// - Understands bracket nesting
    /// - Syncs at closing braces if we're inside a block
    pub(super) fn skip_to_statement_boundary_smart(&mut self) {
        let initial_brace_depth = self.brace_depth();

        while !self.at_end() {
            match self.peek() {
                // Statement keywords - always sync here
                Some(Token::Def) | Some(Token::Meta) | Some(Token::Prim)
                | Some(Token::Namespace) | Some(Token::Open) | Some(Token::Inductive) => {
                    break;
                }

                // Closing brace - only sync if it's at or below our starting depth
                Some(Token::RBrace) => {
                    if self.brace_depth() <= initial_brace_depth {
                        // This brace closes a parent block or our own block - stop here
                        break;
                    } else {
                        // This brace closes a nested block - skip it and continue
                        self.consume(Token::RBrace);
                        self.pop_brace();
                    }
                }

                // Opening brace - track it
                Some(Token::LBrace) => {
                    let loc = self.consume(Token::LBrace);
                    self.push_brace(loc);
                }

                // Track parens too (for completeness)
                Some(Token::LParen) => {
                    let loc = self.consume(Token::LParen);
                    self.push_paren(loc);
                }
                Some(Token::RParen) => {
                    self.consume(Token::RParen);
                    self.pop_paren();
                }

                // Everything else - skip it
                _ => {
                    self.advance();
                }
            }
        }
    }
}
