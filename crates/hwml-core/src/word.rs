use hwml_support::FromWithDb;

#[salsa::interned]
pub struct Word {
    #[return_ref]
    pub text: Box<str>,
}

impl<'db, T> FromWithDb<'db, T> for Word<'db>
where
    T: Into<Box<str>>,
{
    fn from_with_db<Db>(db: &'db Db, value: T) -> Word<'db>
    where
        Db: salsa::Database + ?Sized,
    {
        Word::new(db, value.into())
    }
}
