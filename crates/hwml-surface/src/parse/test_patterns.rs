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
}
