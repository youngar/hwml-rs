use hwml_core::{NameError, QualifiedName};

/// Kinds of global names the elaborator can reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GlobalNameKind {
    Constant,
    Primitive,
    TypeConstructor,
    DataConstructor,
}

/// Build a single-segment `QualifiedName` from a UTF-8 string.
///
/// Parses the segment as a mixfix name with proper fixity detection.
///
/// # Errors
/// Returns error if the segment contains consecutive underscores.
pub fn str_to_simple_qname<'db>(
    db: &'db dyn salsa::Database,
    namespace: Option<QualifiedName<'db>>,
    segment: &str,
) -> Result<QualifiedName<'db>, NameError> {
    let name = hwml_core::str_to_name(db, segment)?;
    Ok(QualifiedName::new(db, namespace, name))
}

/// Build a single-segment `QualifiedName` from UTF-8 bytes.
///
/// **Deprecated**: Use `str_to_simple_qname` instead.
/// This function is kept for backward compatibility during migration.
pub fn bytes_to_simple_qname<'db>(
    db: &'db dyn salsa::Database,
    namespace: Option<QualifiedName<'db>>,
    segment: &[u8],
) -> Result<QualifiedName<'db>, NameError> {
    let text = String::from_utf8_lossy(segment);
    str_to_simple_qname(db, namespace, text.as_ref())
}

/// Build a `QualifiedName` from a dotted path like `Foo.Bar.Baz` under an optional namespace.
///
/// # Errors
/// Returns error if any segment contains consecutive underscores.
pub fn path_to_qname<'db>(
    db: &'db dyn salsa::Database,
    namespace: Option<QualifiedName<'db>>,
    path: &[u8],
) -> Result<QualifiedName<'db>, NameError> {
    let segments: Vec<&[u8]> = path.split(|&b| b == b'.').collect();
    let mut current = namespace;
    for seg in segments {
        current = Some(bytes_to_simple_qname(db, current, seg)?);
    }
    // SAFETY: path is non-empty so segments has at least one element.
    current.ok_or(NameError::EmptyIdentifier)
}
