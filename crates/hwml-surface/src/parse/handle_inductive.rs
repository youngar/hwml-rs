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
        
        // Parse optional indices: : (i : I) -> Type
        let indices = if self.at_token(Token::Colon) {
            self.consume(Token::Colon);
            self.parse_typed_bindings_from_type()
        } else {
            TypedBindings::new(vec![])
        };
        
        // Expect :=
        if !self.at_token(Token::ColonEqual) {
            self.emit_error("Expected ':=' after inductive signature");
            let stmt = self.make_error_statement("Invalid inductive");
            self.push_statement(stmt);
            return;
        }
        self.consume(Token::ColonEqual);
        
        // Parse constructors
        let mut constructors = vec![];
        
        loop {
            // Expect '|' or 'end'
            if self.at_token(Token::End) {
                self.consume(Token::End);
                break;
            }
            
            if !self.at_token(Token::Pipe) {
                if constructors.is_empty() {
                    // First constructor might not have |
                } else {
                    self.emit_error("Expected '|' before constructor or 'end'");
                    break;
                }
            } else {
                self.consume(Token::Pipe);
            }
            
            // Parse constructor name
            if !self.at_token(Token::Identifier) {
                self.emit_error("Expected constructor name");
                break;
            }
            
            let ctor_loc = self.current_location();
            let ctor_name = self.parse_id();

            // Parse constructor type (after ':')
            let ctor_ty = if self.at_token(Token::Colon) {
                self.consume(Token::Colon);
                self.parse_simple_type()
            } else {
                // Constructor with no explicit type
                Box::new(Expression::Hole(ExpressionHole::new(self.current_location(), None)))
            };

            let constructor = Constructor::new(ctor_loc, ctor_name, ctor_ty);
            constructors.push(constructor);
        }
        
        // Universe is always Type for now
        let universe = Box::new(Expression::Universe(crate::syntax::Universe::new(loc.clone(), None)));

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
        if self.at_token(Token::Identifier) {
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
}
