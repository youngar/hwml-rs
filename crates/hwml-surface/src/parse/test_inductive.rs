//! Tests for inductive type parsing

#[cfg(test)]
mod tests {
    use crate::parse::Parser;
    use crate::syntax::*;
    
    #[test]
    fn test_simple_inductive() {
        // Test: inductive Nat : Type := | zero : Nat | succ : Nat -> Nat end
        let input = b"inductive Nat : Type := | zero : Nat | succ : Nat -> Nat end";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        assert_eq!(result.program.statements.len(), 1);
        
        match &result.program.statements[0] {
            Statement::Inductive(ind) => {
                assert_eq!(&*ind.name.value, "Nat");
                
                // No parameters
                assert_eq!(ind.parameters.groups.len(), 0);
                
                // Universe is Type
                match &*ind.universe {
                    Expression::Universe(_) => {
                        // Good
                    }
                    _ => panic!("Expected Universe for inductive type"),
                }
                
                // Two constructors
                assert_eq!(ind.constructors.len(), 2);
                
                // First constructor: zero
                assert_eq!(&*ind.constructors[0].name.value, "zero");
                match &*ind.constructors[0].ty {
                    Expression::Id(id) => {
                        assert_eq!(&*id.value, "Nat");
                    }
                    _ => panic!("Expected Id type for zero"),
                }
                
                // Second constructor: succ
                assert_eq!(&*ind.constructors[1].name.value, "succ");
                // Type should be Nat -> Nat
                match &*ind.constructors[1].ty {
                    Expression::Arrow(_) => {
                        // Good - it's an arrow type
                    }
                    _ => panic!("Expected Arrow type for succ"),
                }
            }
            _ => panic!("Expected Inductive statement"),
        }
    }
    
    #[test]
    fn test_parameterized_inductive() {
        // Test: inductive List (A : Type) : Type := | nil : List A | cons : A -> List A -> List A end
        let input = b"inductive List (A : Type) : Type := | nil : List A | cons : A -> List A -> List A end";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        assert_eq!(result.program.statements.len(), 1);
        
        match &result.program.statements[0] {
            Statement::Inductive(ind) => {
                assert_eq!(&*ind.name.value, "List");
                
                // One parameter group (A : Type)
                assert_eq!(ind.parameters.groups.len(), 1);
                
                let param_group = &ind.parameters.groups[0];
                assert_eq!(param_group.binders.len(), 1);
                
                // Check parameter name
                match &param_group.binders[0].pattern {
                    Pattern::Id(id) => {
                        assert_eq!(&*id.value, "A");
                    }
                    _ => panic!("Expected Id pattern for parameter"),
                }
                
                // Two constructors
                assert_eq!(ind.constructors.len(), 2);
                assert_eq!(&*ind.constructors[0].name.value, "nil");
                assert_eq!(&*ind.constructors[1].name.value, "cons");
            }
            _ => panic!("Expected Inductive statement"),
        }
    }
    
    #[test]
    fn test_empty_inductive() {
        // Test: inductive Empty : Type := end
        let input = b"inductive Empty : Type := end";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        assert_eq!(result.program.statements.len(), 1);
        
        match &result.program.statements[0] {
            Statement::Inductive(ind) => {
                assert_eq!(&*ind.name.value, "Empty");
                
                // No constructors
                assert_eq!(ind.constructors.len(), 0);
            }
            _ => panic!("Expected Inductive statement"),
        }
    }
    
    #[test]
    fn test_multiple_parameters() {
        // Test: inductive Pair (A : Type) (B : Type) : Type := | pair : A -> B -> Pair A B end
        let input = b"inductive Pair (A : Type) (B : Type) : Type := | pair : A -> B -> Pair A B end";
        let parser = Parser::new(input);
        let result = parser.parse();
        
        assert_eq!(result.program.statements.len(), 1);
        
        match &result.program.statements[0] {
            Statement::Inductive(ind) => {
                assert_eq!(&*ind.name.value, "Pair");
                
                // Two parameter groups
                assert_eq!(ind.parameters.groups.len(), 2);
                
                // First parameter: A
                match &ind.parameters.groups[0].binders[0].pattern {
                    Pattern::Id(id) => {
                        assert_eq!(&*id.value, "A");
                    }
                    _ => panic!("Expected Id pattern"),
                }
                
                // Second parameter: B
                match &ind.parameters.groups[1].binders[0].pattern {
                    Pattern::Id(id) => {
                        assert_eq!(&*id.value, "B");
                    }
                    _ => panic!("Expected Id pattern"),
                }
                
                // One constructor
                assert_eq!(ind.constructors.len(), 1);
                assert_eq!(&*ind.constructors[0].name.value, "pair");
            }
            _ => panic!("Expected Inductive statement"),
        }
    }
}
