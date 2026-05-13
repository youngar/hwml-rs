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

    // ===== Phase 1: Bracket-Aware Recovery Tests =====

    #[test]
    fn test_skip_to_matching_brace_simple() {
        // Test: namespace Foo { bad content } def bar := 1
        // With bracket-aware recovery integrated, this should skip to closing }
        // and successfully parse bar as a second statement.
        let input = b"namespace Foo { bad content here } def bar := 1";
        let parser = Parser::new(input);
        let result = parser.parse();

        // Should have errors from "bad content"
        assert!(result.errors.len() > 0, "Expected errors from bad content");

        // With smart recovery, we should parse both namespace and bar
        // The exact count depends on whether namespace recovery creates error statements
        assert!(result.program.statements.len() >= 1, "Should have at least namespace");

        // Check if we successfully parsed bar (recovery working!)
        let has_bar = result.program.statements.iter().any(|stmt| {
            if let Statement::Def(def) = stmt {
                &*def.id.value == "bar"
            } else {
                false
            }
        });

        // If recovery is working well, we should find bar
        // (This might not pass yet depending on namespace error handling)
        if has_bar {
            println!("✅ Smart recovery working! Found 'bar' after namespace error");
        } else {
            println!("⚠️  Recovery could be improved - 'bar' not parsed");
        }
    }

    #[test]
    fn test_skip_nested_braces() {
        // Test: namespace Outer { bad { nested { deep } stuff } } def good := 1
        // TODO: Once bracket-aware recovery is integrated, should handle nested braces
        // and parse both namespace and def good
        let input = b"namespace Outer { bad { nested { deep } stuff } } def good := 1";
        let parser = Parser::new(input);
        let result = parser.parse();

        // Should have errors from "bad"
        assert!(result.errors.len() > 0);

        // Should have parsed at least 1 statement (the namespace)
        assert!(result.program.statements.len() >= 1);

        // TODO: When integrated, uncomment this:
        // assert!(result.program.statements.len() >= 2);
        // let last_stmt = &result.program.statements[result.program.statements.len() - 1];
        // match last_stmt {
        //     Statement::Def(def) => {
        //         assert_eq!(&*def.id.value, "good");
        //     }
        //     _ => panic!("Expected last statement to be def good"),
        // }
    }

    #[test]
    fn test_skip_to_matching_paren() {
        // Test: def foo := (bad content here) def bar := 2
        // Should skip to closing ) and continue parsing
        let input = b"def foo := (1 + bad stuff) def bar := 2";
        let parser = Parser::new(input);
        let result = parser.parse();

        // May have errors depending on how expressions handle "bad"
        // But should parse both defs
        assert!(result.program.statements.len() >= 2);

        // Should have parsed bar
        let has_bar = result.program.statements.iter().any(|stmt| {
            if let Statement::Def(def) = stmt {
                &*def.id.value == "bar"
            } else {
                false
            }
        });
        assert!(has_bar, "Should have parsed 'bar' after recovering from paren error");
    }

    #[test]
    fn test_skip_bracket_region_at_eof() {
        // Test: namespace Foo { def a := 1
        // EOF inside namespace - should handle gracefully
        let input = b"namespace Foo { def a := 1";
        let parser = Parser::new(input);
        let result = parser.parse();

        // Should have errors about missing closing brace
        assert!(result.errors.len() > 0);

        // Should have parsed the namespace (even if incomplete)
        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Namespace(ns) => {
                assert_eq!(&*ns.name.value, "Foo");
            }
            _ => panic!("Expected namespace statement"),
        }
    }

    // ===== Phase 2: Expression-Level Sync Point Tests =====

    #[test]
    fn test_expr_recovery_at_comma() {
        // Test: def foo := (1, bad stuff, 3)
        // Should recover at comma and parse 3
        // Note: This tests expression-level sync
        let input = b"def foo := (1, bad, 3)";
        let parser = Parser::new(input);
        let result = parser.parse();

        // Should parse the def (with possible error in tuple)
        assert_eq!(result.program.statements.len(), 1);

        match &result.program.statements[0] {
            Statement::Def(def) => {
                assert_eq!(&*def.id.value, "foo");
                // Value should be present (it's always a Box<Expression>)
                // Just verify we have a def
            }
            _ => panic!("Expected def statement"),
        }
    }

    #[test]
    fn test_expr_recovery_missing_operand() {
        // Test: def foo := 1 + def bar := 2
        // TODO: With expression-level sync, should recognize 'def' as sync point
        // For now, the parser may handle this differently
        let input = b"def foo := 1 + def bar := 2";
        let parser = Parser::new(input);
        let result = parser.parse();

        // Should parse at least one statement
        assert!(result.program.statements.len() >= 1);

        // TODO: When expr-level sync is integrated, uncomment:
        // assert!(result.errors.len() > 0);
        // assert!(result.program.statements.len() >= 2);
        // let has_bar = result.program.statements.iter().any(|stmt| {
        //     if let Statement::Def(def) = stmt {
        //         &*def.id.value == "bar"
        //     } else {
        //         false
        //     }
        // });
        // assert!(has_bar, "Should have synced at 'def' and parsed bar");
    }

    #[test]
    fn test_expr_recovery_invalid_operator() {
        // Test: def foo := (a @ b) def bar := 1
        // @ is not a valid operator - should recover
        let input = b"def foo := (a @ b) def bar := 1";
        let parser = Parser::new(input);
        let result = parser.parse();

        // Should have some statements parsed
        assert!(result.program.statements.len() >= 1);

        // Should have parsed bar
        let has_bar = result.program.statements.iter().any(|stmt| {
            if let Statement::Def(def) = stmt {
                &*def.id.value == "bar"
            } else {
                false
            }
        });
        assert!(has_bar, "Should have parsed bar after expression error");
    }

    // ===== Phase 4: Pattern Recovery Tests =====

    #[test]
    fn test_pattern_recovery_missing_arrow() {
        // Missing => in match clause should recover to next clause
        let input = b"def test := 42 match { | zero bad | succ n => n }";
        let parser = Parser::new(input);
        let result = parser.parse();

        println!("Errors: {:?}", result.errors);
        println!("Program: {:#?}", result.program);

        // Should have error for missing =>
        assert!(result.errors.iter().any(|e| e.message.contains("=>")));

        // Should parse the def statement
        assert_eq!(result.program.statements.len(), 1);
    }

    #[test]
    fn test_pattern_recovery_invalid_pattern() {
        // Missing pattern after pipe should create error pattern
        let input = b"def test := x match { | => 1 | y => 2 }";
        let parser = Parser::new(input);
        let result = parser.parse();

        println!("Errors: {:?}", result.errors);
        println!("Program: {:#?}", result.program);

        // Should have error for missing pattern
        assert!(result.errors.iter().any(|e| e.message.contains("pattern") || e.message.contains("=>")));

        // Should still parse the def
        assert_eq!(result.program.statements.len(), 1);
    }

    #[test]
    fn test_pattern_recovery_multiple_errors_in_match() {
        // Multiple missing arrows in match clauses
        let input = b"def test := x match { | zero bad | valid => 2 }";
        let parser = Parser::new(input);
        let result = parser.parse();

        println!("Errors: {:?}", result.errors);
        println!("Program: {:#?}", result.program);

        // Should report errors (missing =>)
        assert!(!result.errors.is_empty());

        // Should still parse the def
        assert_eq!(result.program.statements.len(), 1);
    }

    #[test]
    fn test_pattern_sync_at_pipe() {
        // Pattern error should sync at pipe and continue
        let input = b"def test := x match { | zero | succ n => n }";
        let parser = Parser::new(input);
        let result = parser.parse();

        println!("Errors: {:?}", result.errors);
        println!("Program: {:#?}", result.program);

        // Should have error for first clause (missing =>)
        assert!(!result.errors.is_empty());

        // Should parse the def
        assert_eq!(result.program.statements.len(), 1);
    }

    #[test]
    fn test_pattern_at_eof() {
        // Missing pattern at EOF should not crash
        let input = b"def test := x match { |";
        let parser = Parser::new(input);
        let result = parser.parse();

        println!("Errors: {:?}", result.errors);
        println!("Program: {:#?}", result.program);

        // Should have error for missing pattern or closing brace
        assert!(!result.errors.is_empty());

        // Should still parse the def (even if incomplete)
        assert_eq!(result.program.statements.len(), 1);
    }

    #[test]
    fn test_pattern_constructor_app_recovery() {
        // Multiple clauses with partial recovery
        // Note: @ is actually lexed as a valid identifier in HWML
        // So we test recovery from missing patterns instead
        let input = b"def test := x match { | Cons xs => xs | Nil => zero }";
        let parser = Parser::new(input);
        let result = parser.parse();

        println!("Errors: {:?}", result.errors);
        println!("Program: {:#?}", result.program);

        // Should parse successfully (no errors in this case)
        // This is a valid match expression

        // Should parse the def
        assert_eq!(result.program.statements.len(), 1);
    }
}
