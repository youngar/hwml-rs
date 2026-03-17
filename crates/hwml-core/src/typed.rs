pub use crate::*;

#[derive(Debug, Clone)]
pub struct Typed<'db, A> {
    pub subject: A,
    pub ty: RcValue<'db>,
}

pub type TypedSyntax<'db> = Typed<'db, RcSyntax<'db>>;
pub type TypedValue<'db> = Typed<'db, RcValue<'db>>;

impl<'db, A> HasSourceRange<'db> for Typed<'db, A>
where
    A: HasSourceRange<'db>,
{
    fn source_range(&self) -> Option<SourceRange<'db>> {
        self.subject.source_range()
    }
}
