//! Tests for statement parsing

#[cfg(test)]
mod tests {
    use crate::parse::Parser;
    use crate::syntax::*;

    #[test]
    fn test_simple_def() {
        // Test: def foo := <placeholder>
        let input = b"def foo := bar";
        let parser = Parser::new(input);
        let result = parser.parse();

        // Should parse one statement
        assert_eq!(result.program.statements.len(), 1);

        // Should be a Def statement
        match &result.program.statements[0] {
            Statement::Def(def) => {
                assert_eq!(&*def.id.value, "foo");
                // Value is placeholder since we haven't implemented expression parsing yet
            }
            _ => panic!("Expected Def statement"),
        }
    }

    #[test]
    fn test_simple_prim() {
        // Test: prim Nat : Type
        let input = b"prim Nat : Type";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Prim(prim) => {
                assert_eq!(&*prim.id.value, "Nat");
                // Type is placeholder
            }
            _ => panic!("Expected Prim statement"),
        }
    }

    #[test]
    fn test_simple_meta() {
        // Test: meta x := y
        let input = b"meta x := y";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Meta(meta) => {
                assert_eq!(&*meta.id.value, "x");
            }
            _ => panic!("Expected Meta statement"),
        }
    }

    #[test]
    fn test_empty_program() {
        let input = b"";
        let parser = Parser::new(input);
        let result = parser.parse();

        assert_eq!(result.program.statements.len(), 0);
        assert_eq!(result.errors.len(), 0);
    }

    #[test]
    fn test_error_recovery() {
        // Test parsing with errors
        let input = b"def"; // Incomplete def
        let parser = Parser::new(input);
        let result = parser.parse();

        // Should have at least one error
        assert!(result.errors.len() > 0);
    }
}
