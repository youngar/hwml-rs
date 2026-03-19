pub use crate::*;

pub type TypedSyntax<'db> = Typed<'db, RcSyntax<'db>>;
pub type TypedValue<'db> = Typed<'db, RcValue<'db>>;

#[derive(Debug, Clone)]
pub struct Typed<'db, A>(pub A, pub RcValue<'db>);

impl<'db, A> Typed<'db, A> {
    pub fn subject(&self) -> &A {
        &self.0
    }

    pub fn ty(&self) -> &RcValue<'db> {
        &self.1
    }
}

impl<'db, A> HasSourceRange<'db> for Typed<'db, A>
where
    A: HasSourceRange<'db>,
{
    fn source_range(&self) -> Option<SourceRange<'db>> {
        self.subject().source_range()
    }
}
