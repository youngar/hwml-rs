use crate::Name;
use hwml_support::FromWithDb;
use std::ops::Deref;

/// A binding represents a term with a single-variable abstraction.
///
/// This is the fundamental structure for representing λ-abstractions, Π-types, let-bindings,
/// and other constructs that introduce exactly one bound variable into a scope.
///
/// # Structure
///
/// A `Binding` pairs:
/// - A **name** (`Name<'db>`): The binder name for the abstracted variable
/// - A **body** (`A`): The term/expression under the abstraction
///
/// # Semantics
///
/// The body `A` is a term in an **extended context** where the bound variable is in scope.
/// De Bruijn index 0 in the body refers to the variable bound by this `Binding`.
///
/// # Examples
///
/// - **Lambda**: `λx. x + 1` is represented as `Binding { name: "x", body: "x + 1" }`
/// - **Pi type**: `(x : Nat) → Vec x` is `Binding { name: "x", body: "Vec x" }`
/// - **Let**: `let x = 5 in x * 2` uses `Binding { name: "x", body: "x * 2" }`
///
/// # Anonymous Bindings
///
/// When the bound variable is not used in the body, use `Name::anonymous(db)` for the name:
/// ```ignore
/// Binding::new(Name::anonymous(db), body)  // represents `λ_. body`
/// ```
///
/// # Contrast with Other Types
///
/// - **`Cell`** (in `telescope.rs`): Pairs a name with a *type*, used in telescopes
/// - **`DynBinding`**: Binds *multiple* variables (for case branch patterns)
/// - **`Binding`**: Binds exactly *one* variable with a body term
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

/// A dynamic binding represents a term with a multi-variable abstraction.
///
/// Unlike `Binding` which abstracts over exactly one variable, `DynBinding` can bind
/// zero or more variables simultaneously. This is used exclusively for **case expression branches**
/// where a constructor pattern can bind multiple arguments.
///
/// # Structure
///
/// A `DynBinding` contains:
/// - **names** (`Box<[Name<'db>]>`): The names for all bound variables (length = arity)
/// - **arity** (`usize`): The number of variables bound by this abstraction
/// - **body** (`A`): The term under the abstraction
///
/// # Semantics
///
/// The body `A` is a term in an **extended context** with `arity` new variables in scope.
/// De Bruijn indices 0..(arity-1) in the body refer to the variables bound by this `DynBinding`.
///
/// The variables are bound in order:
/// - `names[0]` corresponds to De Bruijn index `arity - 1`
/// - `names[1]` corresponds to De Bruijn index `arity - 2`
/// - ...
/// - `names[arity-1]` corresponds to De Bruijn index 0 (most recently bound)
///
/// # Usage: Case Expression Branches
///
/// Each branch of a case expression has a `DynBinding` whose arity matches the number of
/// arguments to the constructor:
///
/// ```ignore
/// match xs {
///     Nil       => 0              // DynBinding { arity: 0, names: [], body: 0 }
///     Cons(h,t) => h + length(t)  // DynBinding { arity: 2, names: [h,t], body: h + length(t) }
/// }
/// ```
///
/// # Creating DynBindings
///
/// - **`DynBinding::new(db, arity, body)`**: Generates placeholder names `v0, v1, v2, ...`
/// - **`DynBinding::named(names, body)`**: Uses explicit names (arity = names.len())
///
/// # Contrast with Other Types
///
/// - **`Binding`**: Binds exactly *one* variable
/// - **`DynBinding`**: Binds *zero or more* variables (dynamic arity)
/// - **`Cell`**: Pairs a name with a type (no abstraction, used in telescopes)
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct DynBinding<'db, A> {
    pub names: Box<[Name<'db>]>,
    pub arity: usize,
    pub body: A,
}

impl<'db, A> DynBinding<'db, A> {
    /// Create a DynBinding with generated names (v0, v1, etc.).
    /// Use this when you don't have meaningful names (e.g., in quote or pattern matching).
    /// Requires database to create Names.
    pub fn new<Db>(db: &'db Db, arity: usize, body: A) -> Self
    where
        Db: salsa::Database + ?Sized,
    {
        let names: Vec<_> = (0..arity)
            .map(|i| {
                let name_str = format!("v{}", i);
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
