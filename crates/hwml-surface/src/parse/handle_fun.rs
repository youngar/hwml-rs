//! Lambda expression parsing handlers
//!
//! Implements parsing for lambda expressions:
//! fun x => expr
//! fun (x : T) => expr
//! fun x y z => expr

use crate::lex::Token;
use crate::parse::context::Context;
use crate::parse::state::State;
use crate::syntax::{Expression, Fun, Bindings};
use std::ops::Range;

impl<'input> Context<'input> {
    /// Handle after 'fun' keyword - parse bindings
    pub(super) fn handle_fun_after_keyword(&mut self, loc: Range<usize>) {
        // Parse bindings (parameters)
        // Examples:
        //   fun x => ...          (single untyped binding)
        //   fun (x : T) => ...    (single typed binding)
        //   fun x y => ...        (multiple untyped bindings)
        //   fun (x : A) (y : B) => ...  (multiple typed bindings)
        
        let bindings = self.parse_bindings();
        
        // Expect '=>' (fat arrow)
        if !self.at_token(Token::FatArrow) {
            self.emit_error("Expected '=>' after lambda bindings");
            let error_expr = Box::new(Expression::Error(
                crate::syntax::ExpressionError::new(loc, "Invalid lambda".to_string())
            ));
            self.push_expr(error_expr);
            return;
        }
        self.consume(Token::FatArrow);
        
        // Push continuation state (runs AFTER body is parsed)
        self.push_state(State::FunAfterBindings {
            loc,
            bindings,
        });
        
        // Parse body expression (runs FIRST, pushes to expr_stack)
        self.parse_expression(crate::parse::state::Precedence::Lowest);
    }
    
    /// Handle after parsing lambda body - build Fun node
    pub(super) fn handle_fun_after_bindings(&mut self, loc: Range<usize>, bindings: Bindings) {
        // Pop the body expression from expr_stack
        let body = self.pop_expr();
        
        // Build Fun node
        let end_loc = body.loc();
        let fun_expr = Box::new(Expression::Fun(Fun::new(
            loc.start..end_loc.end,
            bindings,
            body,
        )));
        
        // Push to expr_stack
        self.push_expr(fun_expr);
    }
}
