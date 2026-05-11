//! Tests for error recovery

#[cfg(test)]
mod tests {
    use crate::parse::Parser;
    use crate::syntax::*;
    
    #[test]
    fn test_recover_from_invalid_def() {
        // Test: def bad := def good := 1
        // Should recover and parse the second def
        let input = b"def bad := def good := 1";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        // Should have parsed at least the second def
        assert!(result.program.statements.len() >= 1);
        
        // Should have some errors
        assert!(result.errors.len() > 0);
    }
    
    #[test]
    fn test_recover_from_missing_name() {
        // Test: def := 1 def foo := 2
        // Should skip the first invalid def and parse the second
        let input = b"def := 1 def foo := 2";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        // Should have errors
        assert!(result.errors.len() > 0);
        
        // Should still parse the second def
        let has_foo = result.program.statements.iter().any(|stmt| {
            if let Statement::Def(def) = stmt {
                &*def.id.value == "foo"
            } else {
                false
            }
        });
        
        assert!(has_foo, "Should have recovered and parsed 'foo'");
    }
    
    #[test]
    fn test_multiple_statements_with_errors() {
        // Test: def a := 1 def bad def c := 3
        // Should parse a and c, skip bad
        let input = b"def a := 1 def bad def c := 3";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        // Should have some errors
        assert!(result.errors.len() > 0);
        
        // Should have parsed at least 2 statements
        assert!(result.program.statements.len() >= 2);
    }
    
    #[test]
    fn test_recover_in_namespace() {
        // Test: namespace Foo { def bad def good := 1 }
        // Should recover inside namespace
        let input = b"namespace Foo { def bad def good := 1 }";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        // Should have parsed the namespace
        assert_eq!(result.program.statements.len(), 1);
        
        match &result.program.statements[0] {
            Statement::Namespace(ns) => {
                assert_eq!(&*ns.name.value, "Foo");
                // Should have some statements inside (at least tried to parse)
                assert!(ns.statements.len() >= 1);
            }
            _ => panic!("Expected Namespace statement"),
        }
        
        // Should have errors
        assert!(result.errors.len() > 0);
    }
    
    #[test]
    fn test_sync_at_statement_keywords() {
        // Test: garbage def foo := 1
        // Should skip garbage and sync at 'def'
        let input = b"garbage tokens here def foo := 1";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        // Should have errors from the garbage
        assert!(result.errors.len() > 0);
        
        // Should have recovered and parsed foo
        let has_foo = result.program.statements.iter().any(|stmt| {
            if let Statement::Def(def) = stmt {
                &*def.id.value == "foo"
            } else {
                false
            }
        });
        
        assert!(has_foo, "Should have synced at 'def' and parsed 'foo'");
    }
    
    #[test]
    fn test_empty_input() {
        // Test: empty input
        let input = b"";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        // Should have no statements
        assert_eq!(result.program.statements.len(), 0);
        
        // Should have no errors
        assert_eq!(result.errors.len(), 0);
    }
    
    #[test]
    fn test_only_errors() {
        // Test: input with only garbage
        let input = b"this is all garbage";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        // Should have errors
        assert!(result.errors.len() > 0);
        
        // Might have some error statements
        // (depends on recovery strategy)
    }
    
    #[test]
    fn test_recover_from_unmatched_brace() {
        // Test: namespace Foo { def a := 1 namespace Bar { def b := 2 }
        // Missing closing brace for Foo
        let input = b"namespace Foo { def a := 1 namespace Bar { def b := 2 }";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        // Should have errors
        assert!(result.errors.len() > 0);
        
        // Should have parsed at least the namespace
        assert!(result.program.statements.len() >= 1);
    }
}
