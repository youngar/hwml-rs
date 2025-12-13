pub trait FromWithDb<'db, T> {
    #[must_use]
    fn from_with_db<Db>(db: &'db Db, value: T) -> Self
    where
        Db: salsa::Database + ?Sized;
}

impl<'db, T> FromWithDb<'db, T> for T {
    #[inline(always)]
    fn from_with_db<Db>(_db: &'db Db, value: T) -> T
    where
        Db: salsa::Database + ?Sized,
    {
        value
    }
}

pub trait IntoWithDb<'db, T> {
    fn into_with_db<Db>(self, db: &'db Db) -> T
    where
        Db: salsa::Database + ?Sized;
}

impl<'db, T, U> IntoWithDb<'db, U> for T
where
    U: FromWithDb<'db, T>,
{
    #[inline]
    #[track_caller]
    fn into_with_db<Db>(self, db: &'db Db) -> U
    where
        Db: salsa::Database + ?Sized,
    {
        U::from_with_db(db, self)
    }
}
