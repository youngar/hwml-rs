//! Elaborator State Management
//!
//! This module implements the Mazzoli-style elaboration architecture, dividing
//! the elaborator's state into two distinct halves:
//!
//! 1. **Local Context (`ElabEnv`)**: Tracks variables currently in scope and their
//!    semantic types. This grows and shrinks as we traverse binders.
//!
//! 2. **Global Context (`SolverState`)**: Tracks metavariables and deferred constraints.
//!    This strictly grows over the course of elaborating a file.

use hwml_core::ty::Ty;
use hwml_core::*;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

/// Type alias for metavariable IDs
/// Uses u16 to match MetaVariableId::local_index in hwml_core
pub type MetaId = usize;

/// The local elaboration environment.
///
/// Tracks the current scope as we traverse the user's Surface AST.
/// Uses `im::Vector` for O(1) cloning when branching (e.g., in case expressions).
#[derive(Clone, Debug)]
pub struct ElabEnv<'db> {
    /// The names the user wrote (for scope resolution and error messages)
    pub names: im::Vector<String>,

    /// The semantic type of each bound variable (needed for `synth`)
    pub types: im::Vector<Rc<Ty<'db>>>,

    /// The runtime values (usually just neutral variables) used to
    /// evaluate types during elaboration
    pub values: im::Vector<Rc<Value<'db>>>,
}

impl<'db> ElabEnv<'db> {
    /// Creates a fresh, empty environment
    pub fn new() -> Self {
        Self {
            names: im::Vector::new(),
            types: im::Vector::new(),
            values: im::Vector::new(),
        }
    }

    /// Pushes a new bound variable into the context
    pub fn push(&mut self, name: String, ty: Rc<Ty<'db>>, value: Rc<Value<'db>>) {
        self.names.push_back(name);
        self.types.push_back(ty);
        self.values.push_back(value);
    }

    /// Returns the current depth (number of bound variables)
    pub fn depth(&self) -> usize {
        self.names.len()
    }

    /// Looks up a variable by name, returning its index from the end
    pub fn lookup(&self, name: &str) -> Option<usize> {
        self.names.iter().rev().position(|n| n == name)
    }
}

impl<'db> Default for ElabEnv<'db> {
    fn default() -> Self {
        Self::new()
    }
}

/// A deferred constraint in the Mazzoli-style constraint graph
#[derive(Clone, Debug)]
pub enum Constraint<'db> {
    /// Prove that Type A is definitionally equal to Type B
    Unify(Rc<Ty<'db>>, Rc<Ty<'db>>),

    /// Prove that Type A fits inside Universe Level N (Sterling's Rule)
    IsSmall { ty: Rc<Ty<'db>>, max_level: usize },
}

/// The global solver state.
///
/// This is the beating heart of the Mazzoli-style typechecker.
/// It tracks every metavariable the Elaborator creates and every constraint it defers.
#[derive(Debug)]
pub struct SolverState<'db> {
    /// Maps a MetaId to its semantic type.
    /// If we create `?x`, what type is it supposed to be?
    pub meta_types: HashMap<MetaId, Rc<Ty<'db>>>,

    /// Maps a MetaId to its solved value.
    /// None = unsolved, Some(val) = solved.
    pub solutions: HashMap<MetaId, Option<Rc<Value<'db>>>>,

    /// The Mazzoli constraint graph.
    /// These are equations the Elaborator couldn't solve immediately.
    pub constraints: Vec<Constraint<'db>>,
}

impl<'db> SolverState<'db> {
    /// Creates a fresh, empty solver state
    pub fn new() -> Self {
        Self {
            meta_types: HashMap::new(),
            solutions: HashMap::new(),
            constraints: Vec::new(),
        }
    }

    /// Returns the next available metavariable ID
    pub fn next_meta_id(&self) -> MetaId {
        self.meta_types.len()
    }
}

impl<'db> Default for SolverState<'db> {
    fn default() -> Self {
        Self::new()
    }
}

/// The main elaborator driver.
///
/// This struct ties together the local context and global solver state,
/// implementing the bidirectional type-checking algorithm.
pub struct Elaborator<'db> {
    /// The global salsa database containing all definitions
    pub db: &'db GlobalEnv<'db>,

    /// The current local scope
    pub env: ElabEnv<'db>,

    /// The shared, mutable constraint solver state
    pub state: Rc<RefCell<SolverState<'db>>>,
}

impl<'db> Elaborator<'db> {
    /// Creates a new elaborator with an empty environment
    pub fn new(db: &'db GlobalEnv<'db>) -> Self {
        Self {
            db,
            env: ElabEnv::new(),
            state: Rc::new(RefCell::new(SolverState::new())),
        }
    }

    /// Creates a fresh metavariable and tracks its type in the SolverState.
    ///
    /// Returns a `Syntax::Metavariable(id, substitution)` node that can be inserted into the Core AST.
    /// The metavariable is initially unsolved and applied to all variables in the current context.
    pub fn fresh_meta(&self, expected_ty: Rc<Ty<'db>>) -> Rc<Syntax<'db>> {
        let mut state = self.state.borrow_mut();
        let id = state.next_meta_id();

        // Register the metavariable's type and mark it as unsolved
        state.meta_types.insert(id, expected_ty);
        state.solutions.insert(id, None);

        // Create the substitution: apply the metavariable to all variables in scope
        // This is the Mazzoli pattern: ?meta[x0, x1, ..., xn]
        let substitution: Vec<_> = (0..self.env.depth())
            .map(|i| Syntax::variable_rc(i.into()))
            .collect();

        // Return it as a metavariable syntax node
        Syntax::metavariable_rc(MetaVariableId(id), substitution)
    }

    /// Emits a unification constraint to the global solver.
    ///
    /// This defers the proof that `actual` and `expected` are definitionally equal.
    pub fn emit_unify(&self, actual: Rc<Ty<'db>>, expected: Rc<Ty<'db>>) {
        self.state
            .borrow_mut()
            .constraints
            .push(Constraint::Unify(actual, expected));
    }

    /// Synthesizes a type for a surface expression.
    ///
    /// Returns both the elaborated Core syntax and its inferred type.
    pub async fn synth(
        &mut self,
        expr: &hwml_surface::Expression,
    ) -> Result<(Rc<Syntax<'db>>, Rc<Ty<'db>>), ElabError> {
        use hwml_surface::Expression;

        match expr {
            // Software Universe: Type (defaulting to U_0 for now)
            Expression::Universe(u) => {
                let level = u.level.unwrap_or(0) as usize;
                let syn = Rc::new(Syntax::UniverseCode(level));
                let ty = Rc::new(Ty::UniverseType);
                Ok((syn, ty))
            }

            // Variable Lookup
            Expression::Id(id) => {
                use hwml_core::Index;

                // Convert the identifier to a string for lookup
                let name = String::from_utf8_lossy(&id.value).to_string();

                // Search backwards through the environment (most recent binding first)
                if let Some(index) = self.env.names.iter().rev().position(|n| n == &name) {
                    // Create a Variable with the de Bruijn index using the helper
                    let syn = Syntax::variable_rc(Index(index));

                    // Retrieve the semantic type from the parallel vector
                    let actual_index = self.env.names.len() - 1 - index;
                    let ty = self.env.types[actual_index].clone();

                    Ok((syn, ty))
                } else {
                    // TODO: Add global database lookup here later
                    Err(ElabError::NotInScope { name })
                }
            }

            // For all other expressions, we cannot infer a type
            _ => Err(ElabError::CannotInfer),
        }
    }

    /// Checks a surface expression against an expected type.
    ///
    /// Returns the elaborated Core syntax.
    pub async fn check(
        &mut self,
        expr: &hwml_surface::Expression,
        expected: Rc<Ty<'db>>,
    ) -> Result<Rc<Syntax<'db>>, ElabError> {
        // We will add specific push rules (like checking Lambda against Pi) here soon.

        // THE FALLBACK RULE: If we don't have a specific check rule, we pull!
        // This is the fundamental check-to-synth conversion.
        let (syn, actual_ty) = self.synth(expr).await?;
        self.emit_unify(actual_ty, expected);
        Ok(syn)
    }
}

/// Errors that can occur during elaboration
#[derive(Debug, Clone, thiserror::Error)]
pub enum ElabError {
    #[error("type mismatch: expected {expected}, got {actual}")]
    TypeMismatch { expected: String, actual: String },

    #[error("variable not in scope: {name}")]
    NotInScope { name: String },

    #[error("cannot infer type for expression")]
    CannotInfer,

    #[error("universe level too large: {level}")]
    UniverseTooLarge { level: usize },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_elab_env_basic() {
        let mut env = ElabEnv::new();
        assert_eq!(env.depth(), 0);

        // Push a variable (using dummy values)
        let ty = Rc::new(Ty::UniverseType);
        let val = Rc::new(Value::UniverseCode(0));
        env.push("x".to_string(), ty.clone(), val.clone());

        assert_eq!(env.depth(), 1);
        assert_eq!(env.lookup("x"), Some(0));
        assert_eq!(env.lookup("y"), None);
    }

    #[test]
    fn test_solver_state_basic() {
        let state = SolverState::new();
        assert_eq!(state.next_meta_id(), 0);
        assert_eq!(state.meta_types.len(), 0);
        assert_eq!(state.solutions.len(), 0);
        assert_eq!(state.constraints.len(), 0);
    }

    #[test]
    fn test_fresh_meta() {
        let global = GlobalEnv::new();
        let elab = Elaborator::new(&global);

        let ty = Rc::new(Ty::UniverseType);
        let meta = elab.fresh_meta(ty.clone());

        // Verify the metavariable was created
        let state = elab.state.borrow();
        assert_eq!(state.next_meta_id(), 1);
        assert_eq!(state.meta_types.len(), 1);
        assert_eq!(state.solutions.len(), 1);
        // Note: We can't compare Ty values directly since Ty doesn't implement PartialEq
        assert!(state.meta_types.get(&0).is_some());
        assert!(state.solutions.get(&0).is_some());

        // Verify the syntax node was created
        match &*meta {
            Syntax::Metavariable(mv) => {
                assert_eq!(mv.id.0, 0);
                assert_eq!(mv.substitution.len(), 0); // Empty context
            }
            _ => panic!("Expected Metavariable, got {:?}", meta),
        }
    }

    #[test]
    fn test_elab_env_cloning() {
        let mut env1 = ElabEnv::new();
        let ty = Rc::new(Ty::UniverseType);
        let val = Rc::new(Value::UniverseCode(0));
        env1.push("x".to_string(), ty.clone(), val.clone());

        // Clone should be O(1) thanks to im::Vector
        let mut env2 = env1.clone();
        env2.push("y".to_string(), ty.clone(), val.clone());

        // Original should be unchanged
        assert_eq!(env1.depth(), 1);
        assert_eq!(env1.lookup("x"), Some(0));
        assert_eq!(env1.lookup("y"), None);

        // Clone should have both
        assert_eq!(env2.depth(), 2);
        assert_eq!(env2.lookup("x"), Some(1)); // x is now at index 1 from the end
        assert_eq!(env2.lookup("y"), Some(0)); // y is at index 0 from the end
    }

    #[tokio::test]
    async fn test_synth_universe() {
        use hwml_surface::{Expression, Universe};

        let global = GlobalEnv::new();
        let mut elab = Elaborator::new(&global);

        // Create a surface syntax for "Type" (Universe with level 0)
        let expr = Expression::Universe(Universe::new(0..4, Some(0)));

        // Synthesize the type
        let (syn, ty) = elab.synth(&expr).await.expect("synth should succeed");

        // Verify the elaborated syntax is UniverseCode(0)
        match &*syn {
            Syntax::UniverseCode(level) => {
                assert_eq!(*level, 0);
            }
            _ => panic!("Expected UniverseCode, got {:?}", syn),
        }

        // Verify the inferred type is UniverseType
        match &*ty {
            Ty::UniverseType => {
                // Success!
            }
            _ => panic!("Expected UniverseType, got {:?}", ty),
        }
    }

    #[tokio::test]
    async fn test_synth_variable() {
        use hwml_core::Index;
        use hwml_surface::{Expression, Id};

        let global = GlobalEnv::new();
        let mut elab = Elaborator::new(&global);

        // Push a variable "x" into the environment
        let x_ty = Rc::new(Ty::UniverseType);
        let x_val = Rc::new(Value::UniverseCode(0));
        elab.env.push("x".to_string(), x_ty.clone(), x_val);

        // Create a surface syntax for the identifier "x"
        let expr = Expression::Id(Id::new(0..1, "x".as_bytes().into()));

        // Synthesize the type
        let (syn, ty) = elab.synth(&expr).await.expect("synth should succeed");

        // Verify the elaborated syntax is Variable(0)
        match &*syn {
            Syntax::Variable(var) => {
                assert_eq!(var.index, Index(0));
            }
            _ => panic!("Expected Variable, got {:?}", syn),
        }

        // Verify the inferred type matches what we pushed
        match &*ty {
            Ty::UniverseType => {
                // Success!
            }
            _ => panic!("Expected UniverseType, got {:?}", ty),
        }
    }

    #[tokio::test]
    async fn test_check_fallback() {
        use hwml_surface::{Expression, Universe};

        let global = GlobalEnv::new();
        let mut elab = Elaborator::new(&global);

        // Create a surface syntax for "Type"
        let expr = Expression::Universe(Universe::new(0..4, Some(0)));

        // Check it against UniverseType (should succeed via fallback)
        let expected = Rc::new(Ty::UniverseType);
        let syn = elab
            .check(&expr, expected.clone())
            .await
            .expect("check should succeed");

        // Verify the elaborated syntax is UniverseCode(0)
        match &*syn {
            Syntax::UniverseCode(level) => {
                assert_eq!(*level, 0);
            }
            _ => panic!("Expected UniverseCode, got {:?}", syn),
        }

        // Verify a constraint was emitted
        let state = elab.state.borrow();
        assert_eq!(state.constraints.len(), 1);

        // Verify the constraint is Unify(UniverseType, UniverseType)
        match &state.constraints[0] {
            Constraint::Unify(actual, expected_ty) => {
                assert!(matches!(&**actual, Ty::UniverseType));
                assert!(matches!(&**expected_ty, Ty::UniverseType));
            }
            _ => panic!("Expected Unify constraint"),
        }
    }
}
