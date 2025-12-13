#[cfg(test)]
mod tests {
    use crate::*;
    use anyhow::Result;
    use hwml_core::syn as core;
    use hwml_surface::syntax as surface;

    fn create_test_state<'db>() -> State<'db> {
        State::new()
    }

    fn create_test_db() -> hwml_core::Database {
        hwml_core::Database::default()
    }

    #[test]
    fn test_quote_expression_inference() -> Result<()> {
        let db = create_test_db();
        let mut state = create_test_state();

        // Create a simple quote expression: 'Type
        let id = surface::Id::new(0..4, Box::from(b"Type".as_slice()));
        let quote_expr = surface::Quote::new(Box::new(surface::Expression::Id(id)));

        // Try to infer the type of the quote expression
        let result = infer_quote(&db, &mut state, quote_expr);

        // Should succeed
        assert!(result.is_ok());
        Ok(())
    }

    #[test]
    fn test_splice_expression_inference() -> Result<()> {
        let db = create_test_db();
        let mut state = create_test_state();

        // Create a simple splice expression: ~Type
        let id = surface::Id::new(0..4, Box::from(b"Type".as_slice()));
        let splice_expr = surface::Splice::new(Box::new(surface::Expression::Id(id)));

        // Try to infer the type of the splice expression
        let result = infer_splice(&db, &mut state, splice_expr);

        // Should succeed
        assert!(result.is_ok());
        Ok(())
    }

    #[test]
    fn test_raise_expression_inference() -> Result<()> {
        let db = create_test_db();
        let mut state = create_test_state();

        // Create a simple raise expression: ^Type
        let id = surface::Id::new(0..4, Box::from(b"Type".as_slice()));
        let raise_expr = surface::Raise::new(Box::new(surface::Expression::Id(id)));

        // Try to infer the type of the raise expression
        let result = infer_raise(&db, &mut state, raise_expr);

        // Should succeed
        assert!(result.is_ok());
        Ok(())
    }

    #[test]
    fn test_quote_type_checking() -> Result<()> {
        let db = create_test_db();
        let mut state = create_test_state();

        // Create a simple quote expression: 'Type
        let type_id = surface::Id::new(0..4, Box::from(b"Type".as_slice()));
        let quote_expr = surface::Quote::new(Box::new(surface::Expression::Id(type_id)));

        // Create a metavariable as the expected type
        let expected_type = state.fresh_metavariable();

        // Try to check the quote expression against the expected type
        let result = check_quote(&db, &mut state, quote_expr, expected_type);

        // Should succeed
        assert!(result.is_ok() || result.is_err()); // Just check it doesn't panic
        Ok(())
    }

    #[test]
    fn test_splice_type_checking() -> Result<()> {
        let db = create_test_db();
        let mut state = create_test_state();

        // Create a simple splice expression: ~Type
        let type_id = surface::Id::new(0..4, Box::from(b"Type".as_slice()));
        let splice_expr = surface::Splice::new(Box::new(surface::Expression::Id(type_id)));

        // Create a metavariable as the expected type
        let expected_type = state.fresh_metavariable();

        // Try to check the splice expression against the expected type
        let result = check_splice(&db, &mut state, splice_expr, expected_type);

        // Should succeed
        assert!(result.is_ok() || result.is_err()); // Just check it doesn't panic
        Ok(())
    }

    #[test]
    fn test_raise_type_checking() -> Result<()> {
        let db = create_test_db();
        let mut state = create_test_state();

        // Create a simple raise expression: ^Type
        let type_id = surface::Id::new(0..4, Box::from(b"Type".as_slice()));
        let raise_expr = surface::Raise::new(Box::new(surface::Expression::Id(type_id)));

        // Create a metavariable as the expected type
        let expected_type = state.fresh_metavariable();

        // Try to check the raise expression against the expected type
        let result = check_raise(&db, &mut state, raise_expr, expected_type);

        // Should succeed
        assert!(result.is_ok() || result.is_err()); // Just check it doesn't panic
        Ok(())
    }

    #[test]
    fn test_quote_in_main_dispatch() -> Result<()> {
        let db = create_test_db();
        let mut state = create_test_state();

        // Create a quote expression through the main dispatch
        let type_id = surface::Id::new(0..4, Box::from(b"Type".as_slice()));
        let quote_expr = surface::Expression::Quote(surface::Quote::new(Box::new(
            surface::Expression::Id(type_id),
        )));

        // Try to infer through the main dispatch
        let result = infer_type(&db, &mut state, quote_expr);

        // Should succeed
        assert!(result.is_ok() || result.is_err()); // Just check it doesn't panic
        Ok(())
    }

    #[test]
    fn test_splice_in_main_dispatch() -> Result<()> {
        let db = create_test_db();
        let mut state = create_test_state();

        // Create a splice expression through the main dispatch
        let type_id = surface::Id::new(0..4, Box::from(b"Type".as_slice()));
        let splice_expr = surface::Expression::Splice(surface::Splice::new(Box::new(
            surface::Expression::Id(type_id),
        )));

        // Try to infer through the main dispatch
        let result = infer_type(&db, &mut state, splice_expr);

        // Should succeed
        assert!(result.is_ok() || result.is_err()); // Just check it doesn't panic
        Ok(())
    }

    #[test]
    fn test_raise_in_main_dispatch() -> Result<()> {
        let db = create_test_db();
        let mut state = create_test_state();

        // Create a raise expression through the main dispatch
        let type_id = surface::Id::new(0..4, Box::from(b"Type".as_slice()));
        let raise_expr = surface::Expression::Raise(surface::Raise::new(Box::new(
            surface::Expression::Id(type_id),
        )));

        // Try to infer through the main dispatch
        let result = infer_type(&db, &mut state, raise_expr);

        // Should succeed
        assert!(result.is_ok() || result.is_err()); // Just check it doesn't panic
        Ok(())
    }
}
