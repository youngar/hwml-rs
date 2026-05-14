use std::ops::Deref;
use crate::Name;
use hwml_support::FromWithDb;

/// A binder pairs a name with a value of type A.
/// This is the fundamental building block for named bindings in telescopes.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Binder<'db, A> {
    pub name: Name<'db>,
    pub value: A,
}

impl<'db, A> Binder<'db, A> {
    pub fn new(name: Name<'db>, value: A) -> Self {
        Binder { name, value }
    }

    pub fn as_ref(&self) -> Binder<'db, &A> {
        Binder {
            name: self.name,
            value: &self.value,
        }
    }

    pub fn map<F, B>(self, f: F) -> Binder<'db, B>
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
/// The name field stores the variable name for pretty-printing and round-tripping.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Binding<'db, A> {
    pub name: Name<'db>,
    pub body: A,
}

impl<'db, A> Binding<'db, A> {
    /// Create a named binding with the given identifier.
    pub fn new(name: Name<'db>, body: A) -> Self {
        Binding { name, body }
    }

    /// Create an anonymous binding with the wildcard name "_".
    /// Use this when you don't have a meaningful name.
    /// Requires database to create the Name.
    pub fn anonymous<Db>(db: &'db Db, body: A) -> Self
    where
        Db: salsa::Database + ?Sized,
    {
        Binding {
            name: Name::from_with_db(db, "_"),
            body,
        }
    }

    /// Create a named binding from a string (alias for compatibility).
    /// Requires database to create the Name.
    pub fn named<Db>(db: &'db Db, name: &str, body: A) -> Self
    where
        Db: salsa::Database + ?Sized,
    {
        Binding::new(Name::from_with_db(db, name), body)
    }

    pub fn term(&self) -> &A {
        &self.body
    }

    pub fn as_ref(&self) -> Binding<'db, &A> {
        Binding {
            name: self.name,
            body: &self.body,
        }
    }

    pub fn into_inner(self) -> A {
        self.body
    }

    pub fn map<F, B>(self, f: F) -> Binding<'db, B>
    where
        F: FnOnce(A) -> B,
    {
        Binding {
            name: self.name,
            body: f(self.body),
        }
    }
}

impl<'db, A> AsRef<A> for Binding<'db, A> {
    fn as_ref(&self) -> &A {
        &self.body
    }
}

impl<'db, A> Deref for Binding<'db, A> {
    type Target = A;

    fn deref(&self) -> &A {
        &self.body
    }
}

/// A dynamic binding that can bind multiple variables.
/// The arity field indicates how many variables are bound.
/// All binders have names (required).
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct DynBinding<'db, A> {
    pub names: Box<[Name<'db>]>,
    pub arity: usize,
    pub body: A,
}

impl<'db, A> DynBinding<'db, A> {
    /// Create a DynBinding with generated dummy names (_0, _1, etc.).
    /// Use this when you don't have meaningful names (e.g., in quote or pattern matching).
    /// Requires database to create Names.
    pub fn new<Db>(db: &'db Db, arity: usize, body: A) -> Self
    where
        Db: salsa::Database + ?Sized,
    {
        let names: Vec<_> = (0..arity)
            .map(|i| {
                let name_str = format!("_{}", i);
                Name::from_with_db(db, name_str)
            })
            .collect();
        DynBinding {
            names: names.into_boxed_slice(),
            arity,
            body,
        }
    }

    /// Create a DynBinding with the given names.
    /// The arity is determined by the length of the names vector.
    pub fn named(names: Vec<Name<'db>>, body: A) -> Self {
        let arity = names.len();
        DynBinding {
            names: names.into_boxed_slice(),
            arity,
            body,
        }
    }
}

impl<'db, A> Deref for DynBinding<'db, A> {
    type Target = A;

    fn deref(&self) -> &A {
        &self.body
    }
}
