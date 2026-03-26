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

use hwml_core::common::MetaVariableId;
use hwml_core::syn::Syntax;
use hwml_core::ty::Ty;
use hwml_core::val::{GlobalEnv, Value};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

/// Type alias for metavariable IDs
/// Uses u16 to match MetaVariableId::local_index in hwml_core
pub type MetaId = u16;

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
        self.meta_types.len() as u16
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
        Syntax::metavariable_rc(MetaVariableId::new(id), substitution)
    }

    /// Synthesizes a type for a surface expression.
    ///
    /// Returns both the elaborated Core syntax and its inferred type.
    pub async fn synth(
        &mut self,
        _expr: &hwml_surface::Expression,
    ) -> Result<(Rc<Syntax<'db>>, Rc<Ty<'db>>), ElabError> {
        // TODO: Implement bidirectional type synthesis
        todo!("synth: bidirectional type synthesis")
    }

    /// Checks a surface expression against an expected type.
    ///
    /// Returns the elaborated Core syntax.
    pub async fn check(
        &mut self,
        _expr: &hwml_surface::Expression,
        _expected: Rc<Ty<'db>>,
    ) -> Result<Rc<Syntax<'db>>, ElabError> {
        // TODO: Implement bidirectional type checking
        todo!("check: bidirectional type checking")
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
        let val = Rc::new(Value::Prim("test".into()));
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
        assert_eq!(state.meta_types.get(&0), Some(&ty));
        assert!(state.solutions.get(&0).is_some());

        // Verify the syntax node was created
        match &*meta {
            Syntax::Metavariable(mv) => {
                assert_eq!(mv.id.local_index, 0);
                assert_eq!(mv.substitution.len(), 0); // Empty context
            }
            _ => panic!("Expected Metavariable, got {:?}", meta),
        }
    }

    #[test]
    fn test_elab_env_cloning() {
        let mut env1 = ElabEnv::new();
        let ty = Rc::new(Ty::UniverseType);
        let val = Rc::new(Value::Prim("test".into()));
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
}
