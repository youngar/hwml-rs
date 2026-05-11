//! Tests for namespace and open statement parsing

#[cfg(test)]
mod tests {
    use crate::parse::Parser;
    use crate::syntax::*;
    
    #[test]
    fn test_empty_namespace() {
        // Test: namespace Foo { }
        let input = b"namespace Foo { }";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        assert_eq!(result.program.statements.len(), 1);
        
        match &result.program.statements[0] {
            Statement::Namespace(ns) => {
                assert_eq!(&*ns.name.value, "Foo");
                assert_eq!(ns.statements.len(), 0);
            }
            _ => panic!("Expected Namespace statement"),
        }
    }
    
    #[test]
    fn test_namespace_with_def() {
        // Test: namespace Nat { def zero := 0 }
        let input = b"namespace Nat { def zero := 0 }";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        assert_eq!(result.program.statements.len(), 1);
        
        match &result.program.statements[0] {
            Statement::Namespace(ns) => {
                assert_eq!(&*ns.name.value, "Nat");
                assert_eq!(ns.statements.len(), 1);
                
                // Check inner def
                match &ns.statements[0] {
                    Statement::Def(def) => {
                        assert_eq!(&*def.id.value, "zero");
                    }
                    _ => panic!("Expected Def statement inside namespace"),
                }
            }
            _ => panic!("Expected Namespace statement"),
        }
    }
    
    #[test]
    fn test_namespace_multiple_statements() {
        // Test: namespace Nat { def zero := 0 def succ := 1 }
        let input = b"namespace Nat { def zero := 0 def succ := 1 }";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        assert_eq!(result.program.statements.len(), 1);
        
        match &result.program.statements[0] {
            Statement::Namespace(ns) => {
                assert_eq!(&*ns.name.value, "Nat");
                assert_eq!(ns.statements.len(), 2);
                
                // Check first def
                match &ns.statements[0] {
                    Statement::Def(def) => {
                        assert_eq!(&*def.id.value, "zero");
                    }
                    _ => panic!("Expected Def statement"),
                }
                
                // Check second def
                match &ns.statements[1] {
                    Statement::Def(def) => {
                        assert_eq!(&*def.id.value, "succ");
                    }
                    _ => panic!("Expected Def statement"),
                }
            }
            _ => panic!("Expected Namespace statement"),
        }
    }
    
    #[test]
    fn test_simple_open() {
        // Test: open Nat
        let input = b"open Nat";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        assert_eq!(result.program.statements.len(), 1);
        
        match &result.program.statements[0] {
            Statement::Open(open) => {
                assert_eq!(&*open.namespace.value, "Nat");
                assert_eq!(open.modifiers.len(), 0);
                assert!(open.as_alias.is_none());
            }
            _ => panic!("Expected Open statement"),
        }
    }
    
    #[test]
    fn test_open_with_hiding() {
        // Test: open Nat hiding (succ)
        let input = b"open Nat hiding (succ)";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        assert_eq!(result.program.statements.len(), 1);
        
        match &result.program.statements[0] {
            Statement::Open(open) => {
                assert_eq!(&*open.namespace.value, "Nat");
                assert_eq!(open.modifiers.len(), 1);
                
                match &open.modifiers[0] {
                    OpenModifier::Hiding(_, names) => {
                        assert_eq!(names.len(), 1);
                        assert_eq!(&*names[0].value, "succ");
                    }
                    _ => panic!("Expected Hiding modifier"),
                }
            }
            _ => panic!("Expected Open statement"),
        }
    }
    
    #[test]
    fn test_open_with_only() {
        // Test: open Nat only (zero)
        let input = b"open Nat only (zero)";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        assert_eq!(result.program.statements.len(), 1);
        
        match &result.program.statements[0] {
            Statement::Open(open) => {
                assert_eq!(&*open.namespace.value, "Nat");
                assert_eq!(open.modifiers.len(), 1);
                
                match &open.modifiers[0] {
                    OpenModifier::Only(_, names) => {
                        assert_eq!(names.len(), 1);
                        assert_eq!(&*names[0].value, "zero");
                    }
                    _ => panic!("Expected Only modifier"),
                }
            }
            _ => panic!("Expected Open statement"),
        }
    }
}
