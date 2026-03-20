use crate::*;
use hwml_core::*;

struct Application<'db, A, B> {
    source_range: SourceRange<'db>,
    fun: A,
    arg: B,
}

impl<'db, A, B> HasSourceRange<'db> for Application<'db, A, B> {
    fn source_range(&self) -> Option<SourceRange<'db>> {
        self.source_range.clone().into()
    }
}
