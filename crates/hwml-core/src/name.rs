use crate::Word;
use hwml_support::{FromWithDb, IntoWithDb};

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

#[salsa::interned]
pub struct Name {
    pub fixity: Fixity,
    #[return_ref]
    parts: Box<[Atom<'db>]>,
}

impl<'db> Name<'db> {
    pub fn to_string(&self, db: &'db dyn salsa::Database) -> String {
        let fixity = self.fixity(db);
        let mut s = String::new();
        if fixity == Fixity::Infix || fixity == Fixity::Prefix {
            s.push_str("_");
        }

        for atom in self.iter(db) {
            s.push_str(atom.text(db));
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

impl<'db, T> FromWithDb<'db, T> for Name<'db>
where
    T: IntoWithDb<'db, Atom<'db>>,
{
    fn from_with_db<Db>(db: &'db Db, value: T) -> Self
    where
        Db: salsa::Database + ?Sized,
    {
        Name::new(db, Fixity::Closed, Box::from([value.into_with_db(db)]))
    }
}

#[salsa::interned]
pub struct QualifiedName {
    pub namespace: Option<QualifiedName<'db>>,
    pub name: Name<'db>,
}

impl<'db> QualifiedName<'db> {
    pub fn to_string(&self, db: &'db dyn salsa::Database) -> String {
        let mut s = String::new();
        let names = self.segments(db);
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
