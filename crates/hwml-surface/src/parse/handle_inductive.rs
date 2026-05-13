//! Inductive type parsing handlers

use crate::lex::Token;
use crate::parse::context::Context;
use crate::syntax::{Statement, Inductive, Constructor, TypedBindings, Id, Expression, ExpressionHole, App};
use std::ops::Range;

impl<'input> Context<'input> {
    /// Handle inductive start - parse entire inductive synchronously
    pub(super) fn handle_inductive_start(&mut self, loc: Range<usize>) {
        // Parse name
        if !self.at_token(Token::Identifier) {
            self.emit_error("Expected identifier after 'inductive'");
            let stmt = self.make_error_statement("Invalid inductive");
            self.push_statement(stmt);
            return;
        }
        
        let name = self.parse_id();

        // Parse optional parameters: (x : T) (y : U)
        let params = self.parse_typed_bindings_groups();

        // Parse optional universe: : Type or : (i : Nat) -> Type
        // For now, simplified: just expect : Type and ignore it
        let universe = if self.at_token(Token::Colon) {
            self.consume(Token::Colon);
            // Parse the type expression (could be "Type" or "(i : Nat) -> Type")
            self.parse_constructor_type()
        } else {
            Box::new(Expression::Universe(crate::syntax::Universe::new(loc.clone(), None)))
        };

        // Indices are not parsed yet (TODO)
        let indices = TypedBindings::new(vec![]);

        // Expect :=
        if !self.at_token(Token::ColonEqual) {
            self.emit_error("Expected ':=' after inductive signature");
            let stmt = self.make_error_statement("Invalid inductive");
            self.push_statement(stmt);
            return;
        }
        self.consume(Token::ColonEqual);

        // Expect opening brace
        if !self.at_token(Token::LBrace) {
            self.emit_error("Expected '{' after ':=' in inductive declaration");

            // Try to recover: skip to next brace if we can find one
            if !self.at_expr_sync_point() {
                self.skip_to_expr_boundary();
            }

            let stmt = self.make_error_statement("Invalid inductive");
            self.push_statement(stmt);
            return;
        }

        let brace_loc = self.current_location();
        self.consume(Token::LBrace);
        self.push_brace(brace_loc);

        // Parse constructors
        let mut constructors = vec![];

        loop {
            // Expect '|' or '}'
            if self.at_token(Token::RBrace) {
                self.consume(Token::RBrace);
                self.pop_brace();
                break;
            }

            if !self.at_token(Token::Pipe) {
                if constructors.is_empty() {
                    // First constructor might not have |
                } else {
                    self.emit_error("Expected '|' before constructor or '}'");
                    // Try to recover: skip to closing brace or next pipe
                    if !self.at_token(Token::RBrace) && !self.at_end() {
                        self.skip_to_matching_brace();
                    }
                    break;
                }
            } else {
                self.consume(Token::Pipe);
            }

            // Parse constructor name
            if !self.at_token(Token::Identifier) {
                self.emit_error("Expected constructor name");
                // Try to recover: skip to closing brace or next pipe
                while !self.at_end() && !self.at_token(Token::RBrace) && !self.at_token(Token::Pipe) {
                    self.advance();
                }
                if self.at_token(Token::RBrace) {
                    self.consume(Token::RBrace);
                    self.pop_brace();
                }
                break;
            }
            
            let ctor_loc = self.current_location();
            let ctor_name = self.parse_id();

            // Parse constructor type (after ':')
            // For now, use parse_simple_type() which handles identifiers and applications
            // TODO: Convert to async pattern and use full expression parser for arrows
            let ctor_ty = if self.at_token(Token::Colon) {
                self.consume(Token::Colon);
                self.parse_constructor_type()
            } else {
                // Constructor with no explicit type
                Box::new(Expression::Hole(ExpressionHole::new(self.current_location(), None)))
            };

            let constructor = Constructor::new(ctor_loc, ctor_name, ctor_ty);
            constructors.push(constructor);
        }

        // Use the parsed universe
        let inductive = Inductive::new(loc, name, params, indices, universe, constructors);
        self.push_statement(Statement::Inductive(inductive));
    }
    
    /// Helper: Parse typed binding groups like (x y : Nat) (z : Bool)
    fn parse_typed_bindings_groups(&mut self) -> TypedBindings {
        use crate::syntax::{TypedBindingGroup, Binder, Pattern};

        let mut groups = vec![];

        while self.at_token(Token::LParen) {
            self.consume(Token::LParen);

            // Parse names
            let mut binders = vec![];
            while self.at_token(Token::Identifier) && !self.at_token(Token::Colon) {
                let id = self.parse_id();
                let loc = id.loc.clone();
                binders.push(Binder::new(loc, Pattern::Id(id)));
            }

            // Expect ':'
            if self.at_token(Token::Colon) {
                self.consume(Token::Colon);

                // Parse type
                let ty = self.parse_simple_type();

                let group = TypedBindingGroup::new(binders, ty);
                groups.push(group);
            }

            if self.at_token(Token::RParen) {
                self.consume(Token::RParen);
            }
        }

        TypedBindings::new(groups)
    }

    /// Helper: Parse typed bindings from a type expression like (i : Nat) -> Type
    fn parse_typed_bindings_from_type(&mut self) -> TypedBindings {
        // For now, just parse a simple type and return empty bindings
        self.parse_simple_type();
        TypedBindings::new(vec![])
    }
    
    /// Helper: Parse a simple type expression (very basic for now)
    fn parse_simple_type(&mut self) -> Box<Expression> {
        let loc = self.current_location();

        if self.at_token(Token::Type) {
            // Parse Type or Type n
            self.consume(Token::Type);
            let level = if self.at_token(Token::Number) {
                let num_loc = self.current_location();
                let text = std::str::from_utf8(&self.input[num_loc.clone()])
                    .unwrap_or("0");
                self.advance();
                text.parse::<u32>().ok()
            } else {
                None
            };
            Box::new(Expression::Universe(crate::syntax::Universe::new(loc, level)))
        } else if self.at_token(Token::Identifier) {
            let id = self.parse_id();
            let mut elements = vec![Box::new(Expression::Id(id))];

            // Handle application (Type1 Type2 Type3)
            while self.at_token(Token::Identifier) {
                let arg_id = self.parse_id();
                elements.push(Box::new(Expression::Id(arg_id)));
            }

            if elements.len() > 1 {
                let loc = self.current_location();
                Box::new(Expression::App(App::new(loc, elements)))
            } else {
                elements.into_iter().next().unwrap()
            }
        } else {
            Box::new(Expression::Hole(ExpressionHole::new(self.current_location(), None)))
        }
    }

    /// Helper: Parse a constructor type (with arrow support)
    fn parse_constructor_type(&mut self) -> Box<Expression> {
        use crate::syntax::Arrow;

        let start_loc = self.current_location();

        // Parse first element (id or application)
        let mut left = self.parse_simple_type();

        // Handle right-associative arrows: A -> B -> C  means  A -> (B -> C)
        while self.at_token(Token::Arrow) {
            self.consume(Token::Arrow);
            let right = self.parse_constructor_type(); // Recursive for right-associativity
            let end_loc = self.current_location();
            left = Box::new(Expression::Arrow(Arrow::new(start_loc.start..end_loc.end, left, right)));
        }

        left
    }
}
