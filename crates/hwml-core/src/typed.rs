pub use crate::*;

#[derive(Debug, Clone)]
pub struct Typed<'db, A> {
    pub subject: A,
    pub ty: RcValue<'db>,
}

pub type TypedSyntax<'db> = Typed<'db, RcSyntax<'db>>;
