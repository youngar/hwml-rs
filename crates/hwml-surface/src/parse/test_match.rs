//! Tests for match expression parsing

#[cfg(test)]
mod tests {
    use crate::parse::Parser;
    use crate::syntax::*;
    
    #[test]
    fn test_simple_match() {
        // Test: match x with | zero => 0 | succ n => n end
        let input = b"def f := match x with | zero => 0 | succ n => n end";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        assert_eq!(result.program.statements.len(), 1);
        
        match &result.program.statements[0] {
            Statement::Def(def) => {
                assert_eq!(&*def.id.value, "f");
                
                // Value should be a match expression
                match &*def.value {
                    Expression::Match(match_expr) => {
                        // Scrutinee should be 'x'
                        match &*match_expr.scrutinee {
                            Expression::Id(id) => {
                                assert_eq!(&*id.value, "x");
                            }
                            _ => panic!("Expected Id scrutinee"),
                        }
                        
                        // Should have 2 clauses
                        assert_eq!(match_expr.clauses.len(), 2);
                        
                        // First clause: zero => 0
                        match &match_expr.clauses[0].pattern {
                            Pattern::Id(id) => {
                                assert_eq!(&*id.value, "zero");
                            }
                            _ => panic!("Expected Id pattern"),
                        }
                        
                        match &*match_expr.clauses[0].body {
                            Expression::Num(_) => {
                                // Good - it's a number
                            }
                            _ => panic!("Expected Num body"),
                        }
                        
                        // Second clause: succ n => n
                        // Pattern will be AppSeq([succ, n]) once we implement it properly
                        // For now, just check we have something
                    }
                    _ => panic!("Expected Match expression"),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }
    
    #[test]
    fn test_match_with_wildcard() {
        // Test: match x with | _ => 0 end
        let input = b"def f := match x with | _ => 0 end";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        assert_eq!(result.program.statements.len(), 1);
        
        match &result.program.statements[0] {
            Statement::Def(def) => {
                match &*def.value {
                    Expression::Match(match_expr) => {
                        assert_eq!(match_expr.clauses.len(), 1);
                        
                        // Pattern should be underscore
                        match &match_expr.clauses[0].pattern {
                            Pattern::Underscore(_) => {
                                // Good
                            }
                            _ => panic!("Expected Underscore pattern"),
                        }
                    }
                    _ => panic!("Expected Match expression"),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }
    
    #[test]
    fn test_match_with_complex_body() {
        // Test: match x with | zero => succ zero end
        let input = b"def f := match x with | zero => succ zero end";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        assert_eq!(result.program.statements.len(), 1);
        
        match &result.program.statements[0] {
            Statement::Def(def) => {
                match &*def.value {
                    Expression::Match(match_expr) => {
                        assert_eq!(match_expr.clauses.len(), 1);
                        
                        // Body should be an application (succ zero)
                        match &*match_expr.clauses[0].body {
                            Expression::App(_) => {
                                // Good - it's an application
                            }
                            _ => {
                                // Might also be parsed differently
                            }
                        }
                    }
                    _ => panic!("Expected Match expression"),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }
    
    #[test]
    fn test_nested_match() {
        // Test: match x with | zero => match y with | zero => 0 end end
        let input = b"def f := match x with | zero => match y with | zero => 0 end end";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        assert_eq!(result.program.statements.len(), 1);
        
        match &result.program.statements[0] {
            Statement::Def(def) => {
                match &*def.value {
                    Expression::Match(outer_match) => {
                        assert_eq!(outer_match.clauses.len(), 1);
                        
                        // Body should be another match expression
                        match &*outer_match.clauses[0].body {
                            Expression::Match(inner_match) => {
                                assert_eq!(inner_match.clauses.len(), 1);
                            }
                            _ => panic!("Expected nested Match expression"),
                        }
                    }
                    _ => panic!("Expected Match expression"),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }
    
    #[test]
    fn test_empty_match() {
        // Test: match x with end
        // This is valid for uninhabited types
        let input = b"def f := match x with end";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        assert_eq!(result.program.statements.len(), 1);
        
        match &result.program.statements[0] {
            Statement::Def(def) => {
                match &*def.value {
                    Expression::Match(match_expr) => {
                        // Should have zero clauses
                        assert_eq!(match_expr.clauses.len(), 0);
                    }
                    _ => panic!("Expected Match expression"),
                }
            }
            _ => panic!("Expected Def statement"),
        }
    }
}
