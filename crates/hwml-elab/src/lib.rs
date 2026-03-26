//! # hwml-elab: Mazzoli-style Elaborator for HWML
//!
//! This crate implements bidirectional type-checking with a global constraint graph.
//! The elaborator translates surface syntax into the Core language while inferring types.
//!
//! ## Architecture
//!
//! - **ElabEnv**: Local context (names, types, values) using im::Vector for O(1) cloning
//! - **SolverState**: Global constraint graph tracking metavariables and deferred constraints
//! - **Elaborator**: Main driver combining local and global state
//!
//! ## Key Concepts
//!
//! - **Bidirectional Type-Checking**: `synth` infers types, `check` validates against expected types
//! - **Constraint Solving**: Difficult unification problems are deferred to a global solver
//! - **Metavariables**: Unknowns in the type system, represented as `?meta[x0, x1, ..., xn]`

pub mod state;

pub use state::*;
