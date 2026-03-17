use crate::*;

pub use std::ops::Range;

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum SourceInfo<'db> {
    File(Word<'db>),
    Synthetic(Word<'db>),
}

impl<'db> SourceInfo<'db> {
    pub fn title<Db>(&self, db: &'db Db) -> &'db str
    where
        Db: salsa::Database,
    {
        match self {
            SourceInfo::File(name) => name.text(db),
            SourceInfo::Synthetic(name) => name.text(db),
        }
    }
}

#[salsa::interned]
pub struct Source {
    pub info: SourceInfo<'db>,
}

impl<'db> Source<'db> {
    pub fn title<Db>(&self, db: &'db Db) -> &'db str
    where
        Db: salsa::Database,
    {
        self.info(db).title(db)
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct SourceRange<'db> {
    pub source: Source<'db>,
    pub range: Range<usize>,
}

impl<'db> SourceRange<'db> {
    pub fn new(source: Source<'db>, range: Range<usize>) -> SourceRange<'db> {
        SourceRange { source, range }
    }
}

pub trait HasSourceRange<'db> {
    fn source_range(&self) -> Option<SourceRange<'db>>;
}

impl<'db> HasSourceRange<'db> for SourceRange<'db> {
    fn source_range(&self) -> Option<SourceRange<'db>> {
        self.clone().into()
    }
}

pub struct WithSourceRange<'db, A>(pub A, pub Option<SourceRange<'db>>);

impl<'db, A> HasSourceRange<'db> for WithSourceRange<'db, A> {
    fn source_range(&self) -> Option<SourceRange<'db>> {
        self.1.clone()
    }
}
