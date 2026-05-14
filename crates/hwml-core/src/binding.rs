use std::ops::Deref;

/// A binder pairs a name with a value of type A.
/// This is the fundamental building block for named bindings in telescopes.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Binder<A> {
    pub name: String,
    pub value: A,
}

impl<A> Binder<A> {
    pub fn new(name: String, value: A) -> Self {
        Binder { name, value }
    }

    pub fn as_ref(&self) -> Binder<&A> {
        Binder {
            name: self.name.clone(),
            value: &self.value,
        }
    }

    pub fn map<F, B>(self, f: F) -> Binder<B>
    where
        F: FnOnce(A) -> B,
    {
        Binder {
            name: self.name,
            value: f(self.value),
        }
    }
}

/// A simple binding that binds a single variable.
/// The name field stores the variable name (as a string) for pretty-printing and round-tripping.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Binding<A> {
    pub name: String,
    pub body: A,
}

impl<A> Binding<A> {
    /// Create a named binding with the given identifier.
    pub fn new(name: String, body: A) -> Self {
        Binding { name, body }
    }

    /// Create an anonymous binding with the dummy name "_".
    /// Use this when you don't have a meaningful name (e.g., in quote).
    pub fn anonymous(body: A) -> Self {
        Binding {
            name: String::from("_"),
            body,
        }
    }

    /// Create a named binding (alias for `new`).
    pub fn named(name: String, body: A) -> Self {
        Binding::new(name, body)
    }

    pub fn term(&self) -> &A {
        &self.body
    }

    pub fn as_ref(&self) -> Binding<&A> {
        Binding {
            name: self.name.clone(),
            body: &self.body,
        }
    }

    pub fn into_inner(self) -> A {
        self.body
    }

    pub fn map<F, B>(self, f: F) -> Binding<B>
    where
        F: FnOnce(A) -> B,
    {
        Binding {
            name: self.name,
            body: f(self.body),
        }
    }
}

impl<A> AsRef<A> for Binding<A> {
    fn as_ref(&self) -> &A {
        &self.body
    }
}

impl<A> Deref for Binding<A> {
    type Target = A;

    fn deref(&self) -> &A {
        &self.body
    }
}

/// A dynamic binding that can bind multiple variables.
/// The arity field indicates how many variables are bound.
/// All binders have names (required).
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct DynBinding<A> {
    pub names: Box<[String]>,
    pub arity: usize,
    pub body: A,
}

impl<A> DynBinding<A> {
    /// Create a DynBinding with generated dummy names (_0, _1, etc.).
    /// Use this when you don't have meaningful names (e.g., in quote or pattern matching).
    pub fn new(arity: usize, body: A) -> Self {
        let names: Vec<_> = (0..arity).map(|i| format!("_{}", i)).collect();
        DynBinding {
            names: names.into_boxed_slice(),
            arity,
            body,
        }
    }

    /// Create a DynBinding with the given names.
    /// The arity is determined by the length of the names vector.
    pub fn named(names: Vec<String>, body: A) -> Self {
        let arity = names.len();
        DynBinding {
            names: names.into_boxed_slice(),
            arity,
            body,
        }
    }
}

impl<A> Deref for DynBinding<A> {
    type Target = A;

    fn deref(&self) -> &A {
        &self.body
    }
}
