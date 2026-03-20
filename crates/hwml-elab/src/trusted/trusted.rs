use hwml_core::*;
use std::ops::Deref;

// #[derive(Clone, Debug)]
// pub struct Trusted<A>(pub(in crate::trusted) A);

#[derive(Clone, Debug)]
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

pub type TrustedSyntax<'db> = Trusted<RcSyntax<'db>>;
pub type TrustedTypedSyntax<'db> = Trusted<TypedSyntax<'db>>;
pub type TrustedValue<'db> = Trusted<RcValue<'db>>;

pub type TrustedType<'db> = Trusted<SynType<'db>>;
pub type TrustedSemType<'db> = Trusted<SemType<'db>>;
