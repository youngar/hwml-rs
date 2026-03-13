use std::ops::Deref;

/// A simple binding that binds a single variable.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
pub struct Binding<A> {
    pub body: A,
}

impl<A> Binding<A> {
    pub fn new(body: A) -> Self {
        Binding { body }
    }
}

impl<A> Deref for Binding<A> {
    type Target = A;

    fn deref(&self) -> &A {
        &self.body
    }
}

/// A dynamic binding that can bind multiple variables. The arity field indicates how many variables are bound.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct DynBinding<A> {
    pub arity: usize,
    pub body: A,
}

impl<A> DynBinding<A> {
    pub fn new(arity: usize, body: A) -> Self {
        DynBinding { arity, body }
    }
}

impl<A> Deref for DynBinding<A> {
    type Target = A;

    fn deref(&self) -> &A {
        &self.body
    }
}
