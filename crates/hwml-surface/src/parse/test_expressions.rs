//! Tests for expression parsing

#[cfg(test)]
mod tests {
    use crate::parse::Parser;
    use crate::syntax::*;

    #[test]
    fn test_simple_number() {
        // Test: def x := 42
        let input = b"def x := 42";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Def(def) => {
                assert_eq!(&*def.id.value, "x");
                // Check the value is a number
                match &*def.value {
                    Expression::Num(num) => {
                        assert_eq!(&*num.value, "42");
                    }
                    _ => panic!("Expected Num expression, got {:?}", def.value),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }

    #[test]
    fn test_identifier_expression() {
        // Test: def x := foo
        let input = b"def x := foo";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Def(def) => match &*def.value {
                Expression::Id(id) => {
                    assert_eq!(&*id.value, "foo");
                }
                _ => panic!("Expected Id expression"),
            },
            _ => panic!("Expected Def statement"),
        }
    }

    #[test]
    fn test_application() {
        // Test: def x := f a
        let input = b"def x := f a";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Def(def) => {
                match &*def.value {
                    Expression::App(app) => {
                        assert_eq!(app.elements.len(), 2);
                        // First element should be 'f'
                        match &*app.elements[0] {
                            Expression::Id(id) => assert_eq!(&*id.value, "f"),
                            _ => panic!("Expected Id in app"),
                        }
                        // Second element should be 'a'
                        match &*app.elements[1] {
                            Expression::Id(id) => assert_eq!(&*id.value, "a"),
                            _ => panic!("Expected Id in app"),
                        }
                    }
                    _ => panic!("Expected App expression"),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }

    #[test]
    fn test_parenthesized_expression() {
        // Test: def x := (foo)
        let input = b"def x := (foo)";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Def(def) => match &*def.value {
                Expression::Paren(paren) => match &*paren.expr {
                    Expression::Id(id) => assert_eq!(&*id.value, "foo"),
                    _ => panic!("Expected Id inside paren"),
                },
                _ => panic!("Expected Paren expression"),
            },
            _ => panic!("Expected Def statement"),
        }
    }

    #[test]
    fn test_type_expression() {
        // Test: prim Nat : Type
        let input = b"prim Nat : Type";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Prim(prim) => {
                assert_eq!(&*prim.id.value, "Nat");
                match &*prim.ty {
                    Expression::Universe(u) => {
                        assert_eq!(u.level, None); // Type without level
                    }
                    _ => panic!("Expected Universe expression"),
                }
            }
            _ => panic!("Expected Prim statement"),
        }
    }

    #[test]
    fn test_underscore() {
        // Test: def x := _
        let input = b"def x := _";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Def(def) => {
                match &*def.value {
                    Expression::Underscore(_) => {
                        // Good!
                    }
                    _ => panic!("Expected Underscore expression"),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }

    #[test]
    fn test_implicit_pi_type() {
        use hwml_core::common::Icit;

        // Test: def id : Pi {A : Type} (x : A) -> A := ...
        let input = b"def id : Pi {A : Type} (x : A) -> A := _";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Def(def) => {
                assert_eq!(&*def.id.value, "id");

                // Check the type annotation
                match &def.ty {
                    Some(ty_expr) => {
                        match &**ty_expr {
                            Expression::Pi(pi) => {
                                assert_eq!(pi.bindings.groups.len(), 2);

                                // First binding should be implicit: {A : Type}
                                let first = &pi.bindings.groups[0];
                                assert_eq!(first.icit, Icit::Implicit);
                                assert_eq!(first.binders.len(), 1);

                                // Second binding should be explicit: (x : A)
                                let second = &pi.bindings.groups[1];
                                assert_eq!(second.icit, Icit::Explicit);
                                assert_eq!(second.binders.len(), 1);
                            }
                            _ => panic!("Expected Pi expression, got {:?}", ty_expr),
                        }
                    }
                    None => panic!("Expected type annotation"),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }

    #[test]
    fn test_implicit_application() {
        use hwml_core::common::Icit;

        // Test: def test := id {Nat} 42
        let input = b"def test := id {Nat} 42";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Def(def) => {
                assert_eq!(&*def.id.value, "test");

                // Check the value is an application
                match &*def.value {
                    Expression::App(app) => {
                        // Should have 3 elements: id, {Nat}, 42
                        assert_eq!(app.elements.len(), 3);

                        // Should have 2 arg_icits (one for each arg, not the function)
                        assert_eq!(app.arg_icits.len(), 2);

                        // First arg {Nat} should be implicit
                        assert_eq!(app.arg_icits[0], Icit::Implicit);

                        // Second arg 42 should be explicit
                        assert_eq!(app.arg_icits[1], Icit::Explicit);

                        // Verify the function is 'id'
                        match &*app.elements[0] {
                            Expression::Id(id) => {
                                assert_eq!(&*id.value, "id");
                            }
                            _ => panic!("Expected Id for function"),
                        }

                        // Verify first arg is 'Nat'
                        match &*app.elements[1] {
                            Expression::Id(id) => {
                                assert_eq!(&*id.value, "Nat");
                            }
                            _ => panic!("Expected Id for implicit arg"),
                        }

                        // Verify second arg is '42'
                        match &*app.elements[2] {
                            Expression::Num(num) => {
                                assert_eq!(&*num.value, "42");
                            }
                            _ => panic!("Expected Num for explicit arg"),
                        }
                    }
                    _ => panic!("Expected App expression, got {:?}", def.value),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }
}
