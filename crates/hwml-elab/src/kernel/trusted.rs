use hwml_core::syn::Syntax;
use hwml_core::*;
use std::ops::Deref;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct Trusted<A>(pub(in crate::kernel) A);

impl<A> Deref for Trusted<A> {
    type Target = A;

    fn deref(&self) -> &A {
        &self.0
    }
}

pub type TrustSyntax<'db> = Trusted<RcSyntax<'db>>;

/// A trusted term that has been validated by the kernel.
///
/// The inner field is **private**, which means code outside this module
/// cannot construct a `TrustedTerm` directly. This enforces the LCF boundary:
/// only kernel functions can produce trusted terms.
#[derive(Debug)]
pub struct TrustedTerm<'db>(Rc<Syntax<'db>>);

impl<'db> TrustedTerm<'db> {
    /// Safely observe the underlying syntax without allowing modification or forgery.
    ///
    /// This method allows pattern matching on the syntax structure while
    /// maintaining the invariant that only the kernel can construct new terms.
    pub fn view(&self) -> &Syntax<'db> {
        &self.0
    }

    /// **TEMPORARY BACKDOOR**: Used ONLY by the parser and testing prelude.
    ///
    /// The elaborator MUST NOT use this function. This will be removed or
    /// restricted in later phases when the parser is integrated with the kernel.
    ///
    /// # Safety
    /// This function bypasses the kernel's type checking. Use only when you
    /// have externally verified that the syntax is well-formed.
    pub fn assume_trusted(syn: Rc<Syntax<'db>>) -> Self {
        Self(syn)
    }

    /// Get the inner `Rc<Syntax<'db>>` for compatibility during migration.
    ///
    /// This is a temporary method to ease the transition. Eventually, all
    /// code should work with `TrustedTerm` directly and use `view()` for
    /// pattern matching.
    pub fn into_inner(self) -> Rc<Syntax<'db>> {
        self.0
    }

    /// Get a reference to the inner `Rc<Syntax<'db>>` for compatibility.
    pub fn as_inner(&self) -> &Rc<Syntax<'db>> {
        &self.0
    }
}

// Implement PartialEq, Eq, Hash based on the inner Syntax
impl<'db> PartialEq for TrustedTerm<'db> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<'db> Eq for TrustedTerm<'db> {}

impl<'db> std::hash::Hash for TrustedTerm<'db> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
