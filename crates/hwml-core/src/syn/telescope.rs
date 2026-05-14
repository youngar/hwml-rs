use crate::{Binder, Name, RcSyntax};

/// A telescope is a sequence of typed binders where later types can depend on earlier binders.
/// Each binder has a name and a type.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Telescope<'db> {
    /// The binders (name, type pairs).
    pub binders: Box<[Binder<'db, RcSyntax<'db>>]>,
}

impl<'db> Telescope<'db> {
    /// Create a telescope from binders.
    pub fn new<T>(binders: T) -> Self
    where
        T: Into<Box<[Binder<'db, RcSyntax<'db>>]>>,
    {
        Telescope {
            binders: binders.into(),
        }
    }

    /// Create a telescope from (name, type) pairs.
    /// Names can be created from strings via Name::from_with_db.
    pub fn from_pairs<T>(pairs: T) -> Self
    where
        T: IntoIterator<Item = (Name<'db>, RcSyntax<'db>)>,
    {
        let binders: Box<[_]> = pairs
            .into_iter()
            .map(|(name, ty)| Binder::new(name, ty))
            .collect();
        Telescope { binders }
    }

    pub fn len(&self) -> usize {
        self.binders.len()
    }

    pub fn is_empty(&self) -> bool {
        self.binders.is_empty()
    }

    /// Iterator over binders.
    pub fn iter(&self) -> std::slice::Iter<'_, Binder<'db, RcSyntax<'db>>> {
        self.binders.iter()
    }
}

impl<'db> FromIterator<Binder<'db, RcSyntax<'db>>> for Telescope<'db> {
    fn from_iter<T: IntoIterator<Item = Binder<'db, RcSyntax<'db>>>>(iter: T) -> Self {
        Telescope::new(Vec::from_iter(iter))
    }
}

impl<'db> FromIterator<(Name<'db>, RcSyntax<'db>)> for Telescope<'db> {
    fn from_iter<T: IntoIterator<Item = (Name<'db>, RcSyntax<'db>)>>(iter: T) -> Self {
        Telescope::from_pairs(iter)
    }
}

impl<'a, 'db> IntoIterator for &'a Telescope<'db> {
    type Item = &'a Binder<'db, RcSyntax<'db>>;
    type IntoIter = std::slice::Iter<'a, Binder<'db, RcSyntax<'db>>>;

    fn into_iter(self) -> Self::IntoIter {
        self.binders.iter()
    }
}
