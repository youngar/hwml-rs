use crate::Word;
use hwml_support::{FromWithDb, IntoWithDb};

/// Error type for invalid identifier formats.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NameError {
    /// Identifier contains consecutive underscores (e.g., "foo__bar", "___")
    ConsecutiveUnderscores(String),
    /// Empty identifier string
    EmptyIdentifier,
    /// Wildcard pattern used as identifier (single underscore "_" cannot be a declaration name)
    WildcardAsIdentifier,
}

impl std::fmt::Display for NameError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NameError::ConsecutiveUnderscores(s) => {
                write!(f, "Identifier '{}' contains consecutive underscores", s)
            }
            NameError::EmptyIdentifier => write!(f, "Identifier cannot be empty"),
            NameError::WildcardAsIdentifier => {
                write!(f, "Wildcard '_' cannot be used as a declaration name")
            }
        }
    }
}

impl std::error::Error for NameError {}

#[derive(Copy, Clone, Debug, Hash, Eq, Ord, PartialEq, PartialOrd)]
pub struct Atom<'db>(pub Word<'db>);

impl<'db> Atom<'db> {
    pub fn new(s: Word<'db>) -> Self {
        Atom(s)
    }

    pub fn text(&self, db: &'db dyn salsa::Database) -> &str {
        self.0.text(db)
    }
}

impl<'db, T> FromWithDb<'db, T> for Atom<'db>
where
    T: IntoWithDb<'db, Word<'db>>,
{
    fn from_with_db<Db>(db: &'db Db, value: T) -> Self
    where
        Db: salsa::Database + ?Sized,
    {
        Atom::new(value.into_with_db(db))
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, Ord, PartialEq, PartialOrd)]
pub enum Fixity {
    Closed,
    Prefix,
    Postfix,
    Infix,
}

/// Convert a UTF-8 string identifier to a Name with correct Fixity.
///
/// Mixfix parsing rules (Agda-style):
/// - `_foo_bar_` → Infix with parts ["foo", "bar"]
/// - `_foo`      → Prefix with parts ["foo"]
/// - `foo_`      → Postfix with parts ["foo"]
/// - `foo`       → Closed with parts ["foo"]
/// - `my_var`    → Closed with parts ["my", "var"] (can be used in mixfix form)
/// - `_`         → Closed with parts ["_"] (special case: pattern wildcard)
///
/// # Errors
///
/// Returns `Err(NameError::ConsecutiveUnderscores)` if the identifier contains
/// consecutive underscores (e.g., `foo__bar`, `___`).
///
/// Returns `Err(NameError::EmptyIdentifier)` if the string is empty.
///
/// # Examples
///
/// ```
/// use hwml_core::{str_to_name, Fixity, TestDatabase};
///
/// let db = TestDatabase::default();
/// let name = str_to_name(&db, "_+_").unwrap();
/// assert_eq!(name.fixity(&db), Fixity::Infix);
/// ```
pub fn str_to_name<'db, Db>(db: &'db Db, text: &str) -> Result<Name<'db>, NameError>
where
    Db: salsa::Database + ?Sized,
{
    // Validate: reject empty strings
    if text.is_empty() {
        return Err(NameError::EmptyIdentifier);
    }

    // Validate: reject consecutive underscores
    if text.contains("__") {
        return Err(NameError::ConsecutiveUnderscores(text.to_string()));
    }

    // Special case: standalone underscore is not allowed as a valid identifier
    // Use Name::anonymous(db) for anonymous binders instead
    if text == "_" {
        return Err(NameError::WildcardAsIdentifier);
    }

    let starts_with_underscore = text.starts_with('_');
    let ends_with_underscore = text.ends_with('_');

    // Determine fixity based on underscore positions
    let fixity = match (starts_with_underscore, ends_with_underscore) {
        (true, true) => Fixity::Infix,
        (true, false) => Fixity::Prefix,
        (false, true) => Fixity::Postfix,
        (false, false) => Fixity::Closed,
    };

    // Split by underscore to extract name parts (atoms)
    // Since we validated no consecutive underscores, no empty segments will appear
    let parts: Box<[Atom<'db>]> = text
        .split('_')
        .filter(|s| !s.is_empty())
        .map(|part| Atom::new(Word::new(db, part)))
        .collect();

    // Defensive: this should never happen after validation
    debug_assert!(
        !parts.is_empty(),
        "str_to_name produced empty parts after validation"
    );

    Ok(Name::new(db, fixity, parts))
}

#[salsa::interned]
pub struct Name {
    pub fixity: Fixity,
    #[return_ref]
    parts: Box<[Atom<'db>]>,
}

impl<'db> Name<'db> {
    /// Create an anonymous name (empty name with no parts).
    /// Anonymous names should be printed as %level where level is the De Bruijn level.
    pub fn anonymous<Db>(db: &'db Db) -> Self
    where
        Db: salsa::Database + ?Sized,
    {
        Name::new(db, Fixity::Closed, Box::from([]))
    }

    pub fn to_string(&self, db: &'db dyn salsa::Database) -> String {
        let fixity = self.fixity(db);
        let mut s = String::new();
        if fixity == Fixity::Infix || fixity == Fixity::Prefix {
            s.push_str("_");
        }

        // Join atoms with underscore between them
        let mut first = true;
        for atom in self.iter(db) {
            if !first {
                s.push_str("_");
            }
            s.push_str(atom.text(db));
            first = false;
        }

        if fixity == Fixity::Infix || fixity == Fixity::Postfix {
            s.push_str("_");
        }
        s
    }

    pub fn iter<Db>(self, db: &'db Db) -> impl Iterator<Item = Atom<'db>> + 'db
    where
        Db: salsa::Database + ?Sized,
    {
        self.parts(db).iter().copied()
    }

    pub fn len<Db>(&self, db: &'db Db) -> usize
    where
        Db: salsa::Database + ?Sized,
    {
        self.parts(db).len()
    }

    pub fn is_empty<Db>(&self, db: &'db Db) -> bool
    where
        Db: salsa::Database + ?Sized,
    {
        self.len(db) == 0
    }
}

// Specific FromWithDb implementations for Name
// (Removed blanket implementation to avoid conflicts and enforce validation)

impl<'db> FromWithDb<'db, &str> for Name<'db> {
    fn from_with_db<Db>(db: &'db Db, value: &str) -> Self
    where
        Db: salsa::Database + ?Sized,
    {
        // Panic on malformed identifiers - these should be caught by the lexer/parser
        // If a malformed identifier reaches here, it's a compiler bug, not a user error
        str_to_name(db, value).expect("Invalid identifier passed to FromWithDb")
    }
}

impl<'db> FromWithDb<'db, String> for Name<'db> {
    fn from_with_db<Db>(db: &'db Db, value: String) -> Self
    where
        Db: salsa::Database + ?Sized,
    {
        str_to_name(db, &value).expect("Invalid identifier passed to FromWithDb")
    }
}

#[salsa::interned]
pub struct QualifiedName {
    pub namespace: Option<QualifiedName<'db>>,
    pub name: Name<'db>,
}

impl<'db> QualifiedName<'db> {
    pub fn to_string(&self, db: &'db dyn salsa::Database) -> String {
        let names = self.segments(db);
        let mut s = String::new();
        let mut first = true;
        for name in names {
            if !first {
                s.push('/')
            }
            s.push_str(&name.to_string(db));
            first = false;
        }
        s
    }

    pub fn segments<Db>(self, db: &'db Db) -> Vec<Name<'db>>
    where
        Db: salsa::Database + ?Sized,
    {
        let mut names = Vec::new();
        let mut current = Some(self);
        while let Some(qn) = current {
            names.push(qn.name(db));
            current = qn.namespace(db);
        }
        names.reverse();
        names
    }

    pub fn qualify_name<Db, T>(self, db: &'db Db, name: T) -> QualifiedName<'db>
    where
        Db: ?Sized + salsa::Database,
        T: IntoWithDb<'db, Name<'db>>,
    {
        QualifiedName::new(db, Some(self), name.into_with_db(db))
    }

    pub fn qualify_path<Db>(
        db: &'db Db,
        namespace: Option<QualifiedName<'db>>,
        path: &[Name<'db>],
    ) -> Option<Self>
    where
        Db: salsa::Database + ?Sized,
    {
        let mut qualified_name = namespace;
        for segment in path {
            qualified_name = Some(QualifiedName::new(db, qualified_name, *segment));
        }
        qualified_name
    }
}

impl<'db, T> FromWithDb<'db, T> for QualifiedName<'db>
where
    T: IntoWithDb<'db, Name<'db>>,
{
    fn from_with_db<Db>(db: &'db Db, value: T) -> QualifiedName<'db>
    where
        Db: salsa::Database + ?Sized,
    {
        QualifiedName::new(db, None, value.into_with_db(db))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TestDatabase;

    #[test]
    fn test_str_to_name_closed() {
        let db = TestDatabase::default();
        let name = str_to_name(&db, "foo").unwrap();
        assert_eq!(name.fixity(&db), Fixity::Closed);
        assert_eq!(name.len(&db), 1);
        assert_eq!(name.parts(&db)[0].text(&db), "foo");
    }

    #[test]
    fn test_str_to_name_infix() {
        let db = TestDatabase::default();
        let name = str_to_name(&db, "_+_").unwrap();
        assert_eq!(name.fixity(&db), Fixity::Infix);
        assert_eq!(name.len(&db), 1);
        assert_eq!(name.parts(&db)[0].text(&db), "+");
    }

    #[test]
    fn test_str_to_name_prefix() {
        let db = TestDatabase::default();
        let name = str_to_name(&db, "_not").unwrap();
        assert_eq!(name.fixity(&db), Fixity::Prefix);
        assert_eq!(name.len(&db), 1);
        assert_eq!(name.parts(&db)[0].text(&db), "not");
    }

    #[test]
    fn test_str_to_name_postfix() {
        let db = TestDatabase::default();
        let name = str_to_name(&db, "factorial_").unwrap();
        assert_eq!(name.fixity(&db), Fixity::Postfix);
        assert_eq!(name.len(&db), 1);
        assert_eq!(name.parts(&db)[0].text(&db), "factorial");
    }

    #[test]
    fn test_str_to_name_multipart_infix() {
        let db = TestDatabase::default();
        let name = str_to_name(&db, "_if_then_else_").unwrap();
        assert_eq!(name.fixity(&db), Fixity::Infix);
        assert_eq!(name.len(&db), 3);
        assert_eq!(name.parts(&db)[0].text(&db), "if");
        assert_eq!(name.parts(&db)[1].text(&db), "then");
        assert_eq!(name.parts(&db)[2].text(&db), "else");
    }

    #[test]
    fn test_str_to_name_standalone_underscore() {
        let db = TestDatabase::default();
        // "_" is now rejected as a valid Name
        let result = str_to_name(&db, "_");
        assert!(matches!(result, Err(NameError::WildcardAsIdentifier)));
    }

    #[test]
    fn test_str_to_name_closed_multipart() {
        let db = TestDatabase::default();
        let name = str_to_name(&db, "my_variable").unwrap();
        assert_eq!(name.fixity(&db), Fixity::Closed);
        assert_eq!(name.len(&db), 2);
        assert_eq!(name.parts(&db)[0].text(&db), "my");
        assert_eq!(name.parts(&db)[1].text(&db), "variable");
    }

    #[test]
    fn test_str_to_name_consecutive_underscores_error() {
        let db = TestDatabase::default();
        let result = str_to_name(&db, "foo__bar");
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            NameError::ConsecutiveUnderscores(_)
        ));
    }

    #[test]
    fn test_str_to_name_empty_error() {
        let db = TestDatabase::default();
        let result = str_to_name(&db, "");
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), NameError::EmptyIdentifier));
    }

    #[test]
    fn test_str_to_name_roundtrip() {
        let db = TestDatabase::default();

        let test_cases = vec![
            "foo",
            "_+_",
            "_not",
            "factorial_",
            "my_var",
            "_if_then_else_",
            // "_" is now rejected as WildcardAsIdentifier
        ];

        for input in test_cases {
            let name = str_to_name(&db, input).unwrap();
            let output = name.to_string(&db);
            assert_eq!(input, output, "Roundtrip failed for '{}'", input);
        }

        // Test that "_" is properly rejected
        let result = str_to_name(&db, "_");
        assert!(matches!(result, Err(NameError::WildcardAsIdentifier)));
    }

    #[test]
    fn test_mixfix_inductive_names() {
        let db = TestDatabase::default();

        // Test inductive type names with mixfix patterns
        let vec_name = str_to_name(&db, "_Vec_").unwrap();
        assert_eq!(vec_name.fixity(&db), Fixity::Infix);
        assert_eq!(vec_name.to_string(&db), "_Vec_");

        let either_name = str_to_name(&db, "_Either_Or_").unwrap();
        assert_eq!(either_name.fixity(&db), Fixity::Infix);
        // Parts are ["Either", "Or"] - the underscores are just fixity markers
        assert_eq!(either_name.len(&db), 2);
    }

    #[test]
    fn test_namespace_with_underscores() {
        let db = TestDatabase::default();

        // Namespaces can contain underscores (they become closed names)
        let std_lib = str_to_name(&db, "std_lib").unwrap();
        assert_eq!(std_lib.fixity(&db), Fixity::Closed);
        assert_eq!(std_lib.len(&db), 2);
        assert_eq!(std_lib.to_string(&db), "std_lib");
    }

    #[test]
    fn test_consecutive_underscores_in_various_contexts() {
        let db = TestDatabase::default();

        // All of these should fail
        let bad_cases = vec![
            "foo__bar",  // consecutive in middle
            "__foo",     // leading consecutive
            "bar__",     // trailing consecutive
            "a__b__c",   // multiple consecutive pairs
            "___",       // all consecutive
            "foo___bar", // triple consecutive
        ];

        for input in bad_cases {
            let result = str_to_name(&db, input);
            assert!(result.is_err(), "Expected '{}' to fail validation", input);
            if let Err(NameError::ConsecutiveUnderscores(msg)) = result {
                assert!(
                    msg.contains(input),
                    "Error message should mention the input"
                );
            } else {
                panic!("Expected ConsecutiveUnderscores error for '{}'", input);
            }
        }
    }

    #[test]
    fn test_qualified_name_with_mixfix() {
        let db = TestDatabase::default();

        // Build a qualified name with mixfix components
        let std = str_to_name(&db, "Std").unwrap();
        let std_ns = QualifiedName::new(&db, None, std);

        let plus = str_to_name(&db, "_+_").unwrap();
        let std_plus = QualifiedName::new(&db, Some(std_ns), plus);

        // Verify structure
        assert_eq!(plus.fixity(&db), Fixity::Infix);
        assert_eq!(std_plus.name(&db), plus);
        assert_eq!(std_plus.namespace(&db), Some(std_ns));
    }

    #[test]
    fn test_reject_double_underscore_alone() {
        let db = TestDatabase::default();
        let result = str_to_name(&db, "__");
        assert!(matches!(result, Err(NameError::ConsecutiveUnderscores(_))));
    }

    #[test]
    fn test_reject_triple_underscore_alone() {
        let db = TestDatabase::default();
        let result = str_to_name(&db, "___");
        assert!(matches!(result, Err(NameError::ConsecutiveUnderscores(_))));
    }

    #[test]
    fn test_reject_many_underscores_alone() {
        let db = TestDatabase::default();
        let result = str_to_name(&db, "______");
        assert!(matches!(result, Err(NameError::ConsecutiveUnderscores(_))));
    }

    #[test]
    fn test_single_underscore_rejected() {
        let db = TestDatabase::default();
        // Single underscore is not allowed as a valid identifier
        let result = str_to_name(&db, "_");
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), NameError::WildcardAsIdentifier));
    }

    #[test]
    fn test_anonymous_name() {
        let db = TestDatabase::default();
        // Anonymous name has no parts
        let name = Name::anonymous(&db);
        assert_eq!(name.fixity(&db), Fixity::Closed);
        assert_eq!(name.len(&db), 0);
        assert!(name.is_empty(&db));
        assert_eq!(name.to_string(&db), "");
    }
}
