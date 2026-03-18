use hwml_core::Name;
use hwml_support::FromWithDb;
use hwml_surface as surface;

/// Convert a surface Id to a vector of Names (path segments).
pub fn surface_id_to_path<'db>(
    db: &'db dyn salsa::Database,
    id: &surface::Id,
) -> Option<Vec<Name<'db>>> {
    let mut names = Vec::new();
    for segment in id.segments() {
        let segment_str = std::str::from_utf8(segment).ok()?;
        names.push(Name::from_with_db(db, segment_str));
    }

    // An empty path is not valid.
    if names.is_empty() {
        return None;
    }

    Some(names)
}
