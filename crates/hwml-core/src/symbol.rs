use hwml_support::FromWithDb;

/// Salsa-based interned string for the hwml-core AST.
#[salsa::interned]
pub struct InternedString {
    #[return_ref]
    pub text: String,
}

/// Anything convertible to string can be converted to an interned string, using a database.
impl<'db, T> FromWithDb<'db, T> for InternedString<'db>
where
    T: Into<String>,
{
    fn from_with_db<Db>(db: &'db Db, value: T) -> InternedString<'db>
    where
        Db: salsa::Database + ?Sized,
    {
        InternedString::new(db, value.into())
    }
}
