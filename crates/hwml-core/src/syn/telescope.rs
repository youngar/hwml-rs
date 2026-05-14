use crate::{Name, RcSyntax};

/// A cell represents a single typed parameter in a telescope.
///
/// Unlike `Binding` and `DynBinding` which represent **abstractions** (terms that bind variables
/// in a body), a `Cell` is simply a **typed declaration** pairing a name with its type.
/// Cells do not contain a body term; they are used to declare parameters in telescopes.
///
/// # Structure
///
/// A `Cell` pairs:
/// - A **name** (`Name<'db>`): The parameter name
/// - A **ty** (`RcSyntax<'db>`): The type of this parameter
///
/// # Usage: Telescopes
///
/// Cells are the building blocks of **telescopes**, which are sequences of typed parameters
/// where later types can depend on earlier parameters:
///
/// ```ignore
/// // Telescope for: (A : Type) (n : Nat) (xs : Vec A n)
/// Telescope {
///     cells: [
///         Cell { name: "A",  ty: Type },
///         Cell { name: "n",  ty: Nat },
///         Cell { name: "xs", ty: Vec A n },  // depends on A and n
///     ]
/// }
/// ```
///
/// # Contrast with Other Types
///
/// - **`Binding<A>`**: A term with a **single-variable abstraction** (λx. body)
/// - **`DynBinding<A>`**: A term with a **multi-variable abstraction** (case branch)
/// - **`Cell`**: A **typed parameter declaration** (no body, just name : type)
///
/// Think of it this way:
/// - `Binding` and `DynBinding` represent **scopes** (they have a body)
/// - `Cell` represents a **parameter signature** (no body, just the declaration)
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Cell<'db> {
    pub name: Name<'db>,
    pub ty: RcSyntax<'db>,
}

impl<'db> Cell<'db> {
    pub fn new(name: Name<'db>, ty: RcSyntax<'db>) -> Self {
        Cell { name, ty }
    }

    pub fn as_ref(&self) -> Cell<'db> {
        Cell {
            name: self.name,
            ty: self.ty.clone(),
        }
    }

    pub fn map_type<F>(self, f: F) -> Cell<'db>
    where
        F: FnOnce(RcSyntax<'db>) -> RcSyntax<'db>,
    {
        Cell {
            name: self.name,
            ty: f(self.ty),
        }
    }
}

/// A telescope is a sequence of dependent typed parameters.
///
/// Telescopes represent sequences of parameters where **later types can depend on earlier parameters**.
/// This is fundamental for dependent type theory where types can mention values.
///
/// # Structure
///
/// A telescope contains a sequence of `Cell`s (typed parameter declarations):
/// ```ignore
/// Telescope { cells: [Cell₁, Cell₂, ..., Cellₙ] }
/// ```
///
/// Each `Cell` has a name and a type. The type of `Cellᵢ` can reference the names bound by
/// `Cell₁, ..., Cellᵢ₋₁` (all earlier cells in the telescope).
///
/// # Examples
///
/// **Simple telescope** (no dependencies):
/// ```ignore
/// (x : Nat) (y : Bool)
/// // Telescope { cells: [Cell("x", Nat), Cell("y", Bool)] }
/// ```
///
/// **Dependent telescope** (later types depend on earlier parameters):
/// ```ignore
/// (A : Type) (n : Nat) (xs : Vec A n)
/// // Type of xs depends on both A and n
/// ```
///
/// # Use Cases
///
/// Telescopes are used for:
/// - **Function parameters**: `f : (x : A) → (y : B x) → C x y`
/// - **Data constructor arguments**: `Cons : (A : Type) → A → List A → List A`
/// - **Metavariable contexts**: A metavariable `?M` with telescope `Γ` becomes `?M[Γ]`
///
/// # Context Extension
///
/// A telescope extends the typing context. When checking/evaluating under a telescope,
/// you must extend the environment with fresh variables for each cell in order.
///
/// # Contrast with Bindings
///
/// - **`Telescope`**: A sequence of **parameter declarations** (types only, no body)
/// - **`Binding`/`DynBinding`**: A term with an **abstraction** (has a body)
///
/// To convert a telescope to a Pi type, you must construct nested `Binding`s:
/// ```ignore
/// // Telescope: (x : A) (y : B x)
/// // Pi type:   Π(x:A). Π(y:B x). result
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Telescope<'db> {
    /// The cells (typed parameter declarations).
    pub cells: Box<[Cell<'db>]>,
}

impl<'db> Telescope<'db> {
    /// Create a telescope from cells.
    pub fn new<T>(cells: T) -> Self
    where
        T: Into<Box<[Cell<'db>]>>,
    {
        Telescope {
            cells: cells.into(),
        }
    }

    /// Create a telescope from (name, type) pairs.
    /// Names can be created from strings via Name::from_with_db.
    pub fn from_pairs<T>(pairs: T) -> Self
    where
        T: IntoIterator<Item = (Name<'db>, RcSyntax<'db>)>,
    {
        let cells: Box<[_]> = pairs
            .into_iter()
            .map(|(name, ty)| Cell::new(name, ty))
            .collect();
        Telescope { cells }
    }

    pub fn len(&self) -> usize {
        self.cells.len()
    }

    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// Iterator over cells.
    pub fn iter(&self) -> std::slice::Iter<'_, Cell<'db>> {
        self.cells.iter()
    }
}

impl<'db> FromIterator<Cell<'db>> for Telescope<'db> {
    fn from_iter<T: IntoIterator<Item = Cell<'db>>>(iter: T) -> Self {
        Telescope::new(Vec::from_iter(iter))
    }
}

impl<'db> FromIterator<(Name<'db>, RcSyntax<'db>)> for Telescope<'db> {
    fn from_iter<T: IntoIterator<Item = (Name<'db>, RcSyntax<'db>)>>(iter: T) -> Self {
        Telescope::from_pairs(iter)
    }
}

impl<'a, 'db> IntoIterator for &'a Telescope<'db> {
    type Item = &'a Cell<'db>;
    type IntoIter = std::slice::Iter<'a, Cell<'db>>;

    fn into_iter(self) -> Self::IntoIter {
        self.cells.iter()
    }
}
