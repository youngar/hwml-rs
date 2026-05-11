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
            Statement::Def(def) => {
                match &*def.value {
                    Expression::Id(id) => {
                        assert_eq!(&*id.value, "foo");
                    }
                    _ => panic!("Expected Id expression"),
                }
            }
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
            Statement::Def(def) => {
                match &*def.value {
                    Expression::Paren(paren) => {
                        match &*paren.expr {
                            Expression::Id(id) => assert_eq!(&*id.value, "foo"),
                            _ => panic!("Expected Id inside paren"),
                        }
                    }
                    _ => panic!("Expected Paren expression"),
                }
            }
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
}
