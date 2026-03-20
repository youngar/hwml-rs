use hwml_core::*;
use std::borrow::Borrow;
use std::ops::Deref;

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Trusted<A>(pub(crate) A);

impl<A> Trusted<A> {
    pub fn unwrap(self) -> A {
        self.0
    }
}

impl<A> Deref for Trusted<A> {
    type Target = A;

    fn deref(&self) -> &A {
        &self.0
    }
}

impl<A, B> AsRef<B> for Trusted<A>
where
    A: AsRef<B>,
    B: ?Sized,
{
    fn as_ref(&self) -> &B {
        self.deref().as_ref()
    }
}

impl<A> Borrow<A> for Trusted<A> {
    fn borrow(&self) -> &A {
        self.deref()
    }
}

pub type TrustedSyntax<'db> = Trusted<RcSyntax<'db>>;
pub type TrustedTypedSyntax<'db> = Trusted<TypedSyntax<'db>>;
pub type TrustedValue<'db> = Trusted<RcValue<'db>>;

pub type TrustedType<'db> = Trusted<SynType<'db>>;
pub type TrustedSemType<'db> = Trusted<SemType<'db>>;
