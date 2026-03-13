use hwml_core::*;
use std::ops::Deref;

#[derive(Clone, Debug)]
pub struct Trusted<A>(pub(in crate::trusted) A);

impl<A> Deref for Trusted<A> {
    type Target = A;

    fn deref(&self) -> &A {
        &self.0
    }
}

impl<A> Trusted<A> {
    /// **TEMPORARY BACKDOOR**: Used ONLY by the parser and testing prelude.
    ///
    /// The elaborator MUST NOT use this function. This will be removed or
    /// restricted in later phases when the parser is integrated with the kernel.
    ///
    /// # Safety
    /// This function bypasses the kernel's type checking. Use only when you
    /// have externally verified that the syntax is well-formed.
    pub fn assume_trusted(inner: A) -> Self {
        Self(inner)
    }

    /// Get the inner value for compatibility during migration.
    ///
    /// This is a temporary method to ease the transition. Eventually, all
    /// code should work with `Trusted` directly and use `Deref` for
    /// pattern matching.
    pub fn into_inner(self) -> A {
        self.0
    }

    /// Get a reference to the inner value for compatibility.
    pub fn as_inner(&self) -> &A {
        &self.0
    }
}

impl<'db> Trusted<RcSyntax<'db>> {
    /// Safely observe the underlying syntax without allowing modification or forgery.
    ///
    /// This method allows pattern matching on the syntax structure while
    /// maintaining the invariant that only the kernel can construct new terms.
    pub fn view(&self) -> &Syntax<'db> {
        &self.0
    }
}

pub type TrustedSyntax<'db> = Trusted<RcSyntax<'db>>;

pub type TrustedTypedSyntax<'db> = Trusted<TypedSyntax<'db>>;
