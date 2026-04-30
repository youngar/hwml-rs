use hwml_core::{Name, Word, Atom, Fixity};
use hwml_surface::Id;

/// Convert a surface Id to a path of Names.
/// Handles dotted paths like "Foo.Bar.Baz" -> [Foo, Bar, Baz]
pub fn surface_id_to_path<'db>(db: &'db dyn salsa::Database, id: &Id) -> Option<Vec<Name<'db>>> {
    let segments: Vec<&[u8]> = id.value.split(|&b| b == b'.').collect();
    
    if segments.is_empty() {
        return None;
    }
    
    let names: Vec<Name<'db>> = segments
        .into_iter()
        .map(|seg| {
            let text = String::from_utf8_lossy(seg);
            let word = Word::new(db, text.as_ref());
            let atom = Atom::new(word);
            Name::new(db, Fixity::Closed, Box::from([atom]))
        })
        .collect();
    
    Some(names)
}

/// Convert raw bytes to a path of Names.
/// Handles dotted paths like b"Foo.Bar.Baz" -> [Foo, Bar, Baz]
pub fn bytes_to_path<'db>(db: &'db dyn salsa::Database, bytes: &[u8]) -> Vec<Name<'db>> {
    let segments: Vec<&[u8]> = bytes.split(|&b| b == b'.').collect();
    
    segments
        .into_iter()
        .map(|seg| {
            let text = String::from_utf8_lossy(seg);
            let word = Word::new(db, text.as_ref());
            let atom = Atom::new(word);
            Name::new(db, Fixity::Closed, Box::from([atom]))
        })
        .collect()
}
