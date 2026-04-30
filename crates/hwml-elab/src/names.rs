use hwml_core::{Atom, Fixity, Name, QualifiedName, Word};

/// Kinds of global names the elaborator can reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GlobalNameKind {
    Constant,
    Primitive,
    TypeConstructor,
    DataConstructor,
}

/// Build a single-segment `QualifiedName` from UTF-8 bytes.
///
/// Uses `Fixity::Closed` (the default for user-defined identifiers).
pub fn bytes_to_simple_qname<'db>(
    db: &'db dyn salsa::Database,
    namespace: Option<QualifiedName<'db>>,
    segment: &[u8],
) -> QualifiedName<'db> {
    let text = String::from_utf8_lossy(segment);
    let word = Word::new(db, text.as_ref());
    let atom = Atom::new(word);
    let name = Name::new(db, Fixity::Closed, Box::from([atom]));
    QualifiedName::new(db, namespace, name)
}

/// Build a `QualifiedName` from a dotted path like `Foo.Bar.Baz` under an optional namespace.
pub fn path_to_qname<'db>(
    db: &'db dyn salsa::Database,
    namespace: Option<QualifiedName<'db>>,
    path: &[u8],
) -> QualifiedName<'db> {
    let segments: Vec<&[u8]> = path.split(|&b| b == b'.').collect();
    let mut current = namespace;
    for seg in segments {
        current = Some(bytes_to_simple_qname(db, current, seg));
    }
    // SAFETY: path is non-empty so segments has at least one element.
    current.expect("path must be non-empty")
}
