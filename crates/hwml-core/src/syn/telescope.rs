use crate::RcSyntax;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Telescope<'db> {
    pub bindings: Box<[RcSyntax<'db>]>,
}

impl<'db> Telescope<'db> {
    pub fn new<T>(bindings: T) -> Self
    where
        T: Into<Box<[RcSyntax<'db>]>>,
    {
        Telescope {
            bindings: bindings.into(),
        }
    }

    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    pub fn iter(&self) -> std::slice::Iter<'_, RcSyntax<'db>> {
        self.bindings.iter()
    }
}

impl<'db, T> From<T> for Telescope<'db>
where
    T: Into<Box<[RcSyntax<'db>]>>,
{
    fn from(bindings: T) -> Self {
        Telescope::new(bindings.into())
    }
}

impl<'db> FromIterator<RcSyntax<'db>> for Telescope<'db> {
    fn from_iter<T: IntoIterator<Item = RcSyntax<'db>>>(iter: T) -> Self {
        Vec::from_iter(iter).into()
    }
}

impl<'a, 'db> IntoIterator for &'a Telescope<'db> {
    type Item = &'a RcSyntax<'db>;
    type IntoIter = std::slice::Iter<'a, RcSyntax<'db>>;

    fn into_iter(self) -> Self::IntoIter {
        self.bindings.iter()
    }
}
