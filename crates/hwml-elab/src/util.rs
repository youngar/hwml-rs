use hwml_core::{Name, NameError};
use hwml_surface::Id;

/// Convert a UTF-8 string to a path of Names.
/// Handles dotted paths like "Foo.Bar.Baz" -> [Foo, Bar, Baz]
/// Returns an empty vector for empty strings or strings containing only dots.
///
/// # Errors
/// Returns error if any path segment contains consecutive underscores.
pub fn str_to_path<'db>(
    db: &'db dyn salsa::Database,
    text: &str,
) -> Result<Vec<Name<'db>>, NameError> {
    text.split('.')
        .filter(|seg| !seg.is_empty())
        .map(|seg| hwml_core::str_to_name(db, seg))
        .collect()
}

/// Convert a surface Id to a path of Names for use in declarations.
/// Handles dotted paths like "Foo.Bar.Baz" -> [Foo, Bar, Baz]
///
/// # Errors
/// Returns error if:
/// - Any path segment contains consecutive underscores
/// - The identifier is empty or contains only dots
/// - The identifier is a single underscore (wildcard pattern)
///
/// # Wildcard Rejection
/// Unlike pattern contexts where `_` is valid, declaration names must be concrete identifiers.
/// This function rejects paths that contain wildcards in any segment.
pub fn surface_id_to_path<'db>(
    db: &'db dyn salsa::Database,
    id: &Id,
) -> Result<Vec<Name<'db>>, NameError> {
    // Check for wildcard pattern in any segment
    // Split by '.' to check each component
    for segment in id.value.split('.').filter(|s| !s.is_empty()) {
        if segment == "_" {
            return Err(NameError::WildcardAsIdentifier);
        }
    }

    str_to_path(db, &id.value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use hwml_core::TestDatabase;

    #[test]
    fn test_surface_id_to_path_rejects_wildcard() {
        let db = TestDatabase::default();
        let id = Id {
            value: "_".into(),
            loc: 0..1,
        };

        let result = surface_id_to_path(&db, &id);
        assert!(matches!(result, Err(NameError::WildcardAsIdentifier)));
    }

    #[test]
    fn test_surface_id_to_path_rejects_wildcard_in_path() {
        let db = TestDatabase::default();
        let id = Id {
            value: "Foo._.Bar".into(),
            loc: 0..9,
        };

        let result = surface_id_to_path(&db, &id);
        assert!(matches!(result, Err(NameError::WildcardAsIdentifier)));
    }

    #[test]
    fn test_surface_id_to_path_accepts_valid_names() {
        let db = TestDatabase::default();
        let id = Id {
            value: "Foo.Bar".into(),
            loc: 0..7,
        };

        let result = surface_id_to_path(&db, &id);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().len(), 2);
    }

    #[test]
    fn test_surface_id_to_path_accepts_mixfix() {
        let db = TestDatabase::default();
        let id = Id {
            value: "_+_".into(),
            loc: 0..3,
        };

        let result = surface_id_to_path(&db, &id);
        // Mixfix names like "_+_" should be accepted (they have content between underscores)
        assert!(result.is_ok());
    }

    #[test]
    fn test_surface_id_to_path_rejects_consecutive_underscores() {
        let db = TestDatabase::default();
        let id = Id {
            value: "foo__bar".into(),
            loc: 0..8,
        };

        let result = surface_id_to_path(&db, &id);
        assert!(matches!(result, Err(NameError::ConsecutiveUnderscores(_))));
    }

    #[test]
    fn test_surface_id_to_path_rejects_double_underscore_alone() {
        let db = TestDatabase::default();
        let id = Id {
            value: "__".into(),
            loc: 0..2,
        };

        let result = surface_id_to_path(&db, &id);
        assert!(matches!(result, Err(NameError::ConsecutiveUnderscores(_))));
    }

    #[test]
    fn test_surface_id_to_path_rejects_triple_underscore() {
        let db = TestDatabase::default();
        let id = Id {
            value: "___".into(),
            loc: 0..3,
        };

        let result = surface_id_to_path(&db, &id);
        assert!(matches!(result, Err(NameError::ConsecutiveUnderscores(_))));
    }

    #[test]
    fn test_surface_id_to_path_rejects_double_underscore_in_path() {
        let db = TestDatabase::default();
        let id = Id {
            value: "Foo.__.Bar".into(),
            loc: 0..10,
        };

        let result = surface_id_to_path(&db, &id);
        assert!(matches!(result, Err(NameError::ConsecutiveUnderscores(_))));
    }
}
