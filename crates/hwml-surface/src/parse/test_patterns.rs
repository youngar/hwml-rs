//! Tests for pattern and binding parsing

#[cfg(test)]
mod tests {
    use crate::parse::Parser;
    use crate::syntax::*;

    #[test]
    fn test_simple_binding() {
        // Test: def f x := x
        let input = b"def f x := x";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Def(def) => {
                assert_eq!(&*def.id.value, "f");

                // Should have one untyped binding group with one binder
                assert_eq!(def.bindings.groups.len(), 1);
                match &def.bindings.groups[0] {
                    BindingGroup::Untyped(group) => {
                        assert_eq!(group.binders.len(), 1);
                        // The binder should have a pattern
                        match &group.binders[0].pattern {
                            Pattern::Id(id) => {
                                assert_eq!(&*id.value, "x");
                            }
                            _ => panic!("Expected Id pattern"),
                        }
                    }
                    _ => panic!("Expected untyped binding group"),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }

    #[test]
    fn test_typed_binding() {
        // Test: def f (x : Nat) := x
        let input = b"def f (x : Nat) := x";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Def(def) => {
                assert_eq!(&*def.id.value, "f");

                // Should have one typed binding group
                assert_eq!(def.bindings.groups.len(), 1);
                match &def.bindings.groups[0] {
                    BindingGroup::Typed(group) => {
                        assert_eq!(group.binders.len(), 1);
                        // Check the binder pattern
                        match &group.binders[0].pattern {
                            Pattern::Id(id) => {
                                assert_eq!(&*id.value, "x");
                            }
                            _ => panic!("Expected Id pattern"),
                        }
                        // Check the type
                        match &*group.ty {
                            Expression::Id(id) => {
                                assert_eq!(&*id.value, "Nat");
                            }
                            _ => panic!("Expected Id type"),
                        }
                    }
                    _ => panic!("Expected typed binding group"),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }

    #[test]
    fn test_multiple_binders() {
        // Test: def f x y z := x
        let input = b"def f x y z := x";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Def(def) => {
                assert_eq!(&*def.id.value, "f");

                // Should have three untyped binding groups (one per parameter)
                assert_eq!(def.bindings.groups.len(), 3);
            }
            _ => panic!("Expected Def statement"),
        }
    }

    #[test]
    fn test_multiple_typed_binders() {
        // Test: def f (x y : Nat) := x
        let input = b"def f (x y : Nat) := x";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Def(def) => {
                assert_eq!(&*def.id.value, "f");

                // Should have one typed binding group with two binders
                assert_eq!(def.bindings.groups.len(), 1);
                match &def.bindings.groups[0] {
                    BindingGroup::Typed(group) => {
                        assert_eq!(group.binders.len(), 2);
                        // Check first binder
                        match &group.binders[0].pattern {
                            Pattern::Id(id) => {
                                assert_eq!(&*id.value, "x");
                            }
                            _ => panic!("Expected Id pattern"),
                        }
                        // Check second binder
                        match &group.binders[1].pattern {
                            Pattern::Id(id) => {
                                assert_eq!(&*id.value, "y");
                            }
                            _ => panic!("Expected Id pattern"),
                        }
                    }
                    _ => panic!("Expected typed binding group"),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }

    #[test]
    fn test_pattern_with_underscore() {
        // Test: def f _ := 0
        let input = b"def f _ := 0";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Def(def) => {
                assert_eq!(&*def.id.value, "f");

                // Should have one untyped binding with underscore
                assert_eq!(def.bindings.groups.len(), 1);
                match &def.bindings.groups[0] {
                    BindingGroup::Untyped(group) => {
                        match &group.binders[0].pattern {
                            Pattern::Underscore(_) => {
                                // Good!
                            }
                            _ => panic!("Expected Underscore pattern"),
                        }
                    }
                    _ => panic!("Expected untyped binding group"),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }

    #[test]
    fn test_tuple_parameters_in_pi_type() {
        // Test: def T : Type := Pi (x y : Nat) -> Bool
        let input = b"def T : Type := Pi (x y : Nat) -> Bool";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);
        assert_eq!(result.errors.len(), 0);

        // Verify it parsed as a Pi type with tuple parameters
        match &result.program.statements[0] {
            Statement::Def(def) => {
                assert_eq!(&*def.id.value, "T");
                // The value should be a Pi expression
                match &*def.value {
                    Expression::Pi(pi) => {
                        // Should have one binding group with two binders
                        assert_eq!(pi.bindings.groups.len(), 1);
                        assert_eq!(pi.bindings.groups[0].binders.len(), 2);

                        // Check binder names
                        match &pi.bindings.groups[0].binders[0].pattern {
                            Pattern::Id(id) => assert_eq!(&*id.value, "x"),
                            _ => panic!("Expected Id pattern"),
                        }
                        match &pi.bindings.groups[0].binders[1].pattern {
                            Pattern::Id(id) => assert_eq!(&*id.value, "y"),
                            _ => panic!("Expected Id pattern"),
                        }

                        // Check type is Nat
                        match &*pi.bindings.groups[0].ty {
                            Expression::Id(id) => assert_eq!(&*id.value, "Nat"),
                            _ => panic!("Expected Nat type"),
                        }
                    }
                    _ => panic!("Expected Pi expression"),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }

    #[test]
    fn test_tuple_parameters_multiple_groups() {
        // Test: def f (x y : Nat) (z w : Bool) := x
        let input = b"def f (x y : Nat) (z w : Bool) := x";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Def(def) => {
                assert_eq!(&*def.id.value, "f");

                // Should have two typed binding groups
                assert_eq!(def.bindings.groups.len(), 2);

                // First group: (x y : Nat)
                match &def.bindings.groups[0] {
                    BindingGroup::Typed(group) => {
                        assert_eq!(group.binders.len(), 2);
                        match &group.binders[0].pattern {
                            Pattern::Id(id) => assert_eq!(&*id.value, "x"),
                            _ => panic!("Expected Id pattern"),
                        }
                        match &group.binders[1].pattern {
                            Pattern::Id(id) => assert_eq!(&*id.value, "y"),
                            _ => panic!("Expected Id pattern"),
                        }
                        match &*group.ty {
                            Expression::Id(id) => assert_eq!(&*id.value, "Nat"),
                            _ => panic!("Expected Nat type"),
                        }
                    }
                    _ => panic!("Expected typed binding group"),
                }

                // Second group: (z w : Bool)
                match &def.bindings.groups[1] {
                    BindingGroup::Typed(group) => {
                        assert_eq!(group.binders.len(), 2);
                        match &group.binders[0].pattern {
                            Pattern::Id(id) => assert_eq!(&*id.value, "z"),
                            _ => panic!("Expected Id pattern"),
                        }
                        match &group.binders[1].pattern {
                            Pattern::Id(id) => assert_eq!(&*id.value, "w"),
                            _ => panic!("Expected Id pattern"),
                        }
                        match &*group.ty {
                            Expression::Id(id) => assert_eq!(&*id.value, "Bool"),
                            _ => panic!("Expected Bool type"),
                        }
                    }
                    _ => panic!("Expected typed binding group"),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }

    #[test]
    fn test_mixed_typed_untyped_bindings() {
        // Test: def f (x y : Nat) z := x
        let input = b"def f (x y : Nat) z := x";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Def(def) => {
                assert_eq!(&*def.id.value, "f");

                // Should have two binding groups: one typed, one untyped
                assert_eq!(def.bindings.groups.len(), 2);

                // First group: (x y : Nat) - typed
                match &def.bindings.groups[0] {
                    BindingGroup::Typed(group) => {
                        assert_eq!(group.binders.len(), 2);
                    }
                    _ => panic!("Expected typed binding group"),
                }

                // Second group: z - untyped
                match &def.bindings.groups[1] {
                    BindingGroup::Untyped(group) => {
                        assert_eq!(group.binders.len(), 1);
                        match &group.binders[0].pattern {
                            Pattern::Id(id) => assert_eq!(&*id.value, "z"),
                            _ => panic!("Expected Id pattern"),
                        }
                    }
                    _ => panic!("Expected untyped binding group"),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }

    #[test]
    fn test_three_tuple_parameters() {
        // Test: def f (x y z : Nat) := x
        let input = b"def f (x y z : Nat) := x";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Def(def) => {
                assert_eq!(&*def.id.value, "f");

                // Should have one typed binding group with three binders
                assert_eq!(def.bindings.groups.len(), 1);
                match &def.bindings.groups[0] {
                    BindingGroup::Typed(group) => {
                        assert_eq!(group.binders.len(), 3);
                        // Check all three binders
                        match &group.binders[0].pattern {
                            Pattern::Id(id) => assert_eq!(&*id.value, "x"),
                            _ => panic!("Expected Id pattern"),
                        }
                        match &group.binders[1].pattern {
                            Pattern::Id(id) => assert_eq!(&*id.value, "y"),
                            _ => panic!("Expected Id pattern"),
                        }
                        match &group.binders[2].pattern {
                            Pattern::Id(id) => assert_eq!(&*id.value, "z"),
                            _ => panic!("Expected Id pattern"),
                        }
                    }
                    _ => panic!("Expected typed binding group"),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }
}
