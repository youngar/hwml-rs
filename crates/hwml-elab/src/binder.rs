use crate::*;
use hwml_core::*;

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Binder<'db> {
    pub source_range: Option<SourceRange<'db>>,
    pub name: Option<Name<'db>>,
}

impl<'db> HasSourceRange<'db> for Binder<'db> {
    fn source_range(&self) -> Option<SourceRange<'db>> {
        self.source_range.clone()
    }
}

pub type TypedBinder<'db> = Typed<'db, Binder<'db>>;
