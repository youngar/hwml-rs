use crate::{Binder, RcSyntax};

/// A telescope is a sequence of typed binders where later types can depend on earlier binders.
/// Each binder has a name and a type.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Telescope<'db> {
    /// The binders (name, type pairs).
    pub binders: Box<[Binder<RcSyntax<'db>>]>,
}

impl<'db> Telescope<'db> {
    /// Create a telescope from binders.
    pub fn new<T>(binders: T) -> Self
    where
        T: Into<Box<[Binder<RcSyntax<'db>>]>>,
    {
        Telescope {
            binders: binders.into(),
        }
    }

    /// Create a telescope from (name, type) pairs.
    pub fn from_pairs<T>(pairs: T) -> Self
    where
        T: IntoIterator<Item = (String, RcSyntax<'db>)>,
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
    pub fn iter(&self) -> std::slice::Iter<'_, Binder<RcSyntax<'db>>> {
        self.binders.iter()
    }
}

impl<'db> FromIterator<Binder<RcSyntax<'db>>> for Telescope<'db> {
    fn from_iter<T: IntoIterator<Item = Binder<RcSyntax<'db>>>>(iter: T) -> Self {
        Telescope::new(Vec::from_iter(iter))
    }
}

impl<'db> FromIterator<(String, RcSyntax<'db>)> for Telescope<'db> {
    fn from_iter<T: IntoIterator<Item = (String, RcSyntax<'db>)>>(iter: T) -> Self {
        Telescope::from_pairs(iter)
    }
}

impl<'a, 'db> IntoIterator for &'a Telescope<'db> {
    type Item = &'a Binder<RcSyntax<'db>>;
    type IntoIter = std::slice::Iter<'a, Binder<RcSyntax<'db>>>;

    fn into_iter(self) -> Self::IntoIter {
        self.binders.iter()
    }
}
