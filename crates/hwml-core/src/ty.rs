//! Semantic Type System (Quadrant 3: Types as a separate domain)
//!
//! This module implements the semantic type system using the Tarski-style
//! universe hierarchy. Types are separate from terms, and type codes (which
//! are terms) are decoded into semantic types via the `El` constructor.
//!
//! ## Architecture
//!
//! - `Ty`: Semantic types (what the unifier operates on)
//! - `TyClosure`: Closures that produce types when applied to values
//! - Type codes live in `Syntax` and `Value` (they are terms!)
//! - `Ty::El(code)` decodes a type code into a semantic type
//!
//! ## Universe Hierarchy
//!
//! ```text
//! UniverseType : ???  (The type of Type 0, Type 1, ...)
//! Type 0 : UniverseType
//! Type 1 : UniverseType
//! Nat : Type 0
//! Vec : Type 0 -> Nat -> Type 0
//! ```

use crate::val::{LocalEnv, RcValue};
use std::rc::Rc;

pub type RcTy<'db> = Rc<Ty<'db>>;

/// Semantic types (evaluated, top-level)
///
/// This is what the unifier and typechecker operate on. It contains NO universe
/// levels - those live in the type codes (inside `El`).
///
/// The key insight: Types are NOT the same as terms. Type codes are terms that
/// evaluate to values, and `El` decodes those values into semantic types.
#[derive(Clone, Debug)]
pub enum Ty<'db> {
    // ========== Universe Types (The Classifiers) ==========
    /// The type of Type 0, Type 1, Type 2, ...
    /// This is the "type of types" - it classifies universe codes.
    UniverseType,

    /// The type of Signal (hardware signal universe)
    SignalUniverseType,

    /// The type of Module (hardware module universe)
    ModuleUniverseType,

    // ========== Top-Level Type Formers ==========
    /// Dependent function type: (x : A) -> B
    ///
    /// The domain is a type, the codomain is a TYPE CLOSURE that depends on
    /// a VALUE (not a type!). This is the key to dependent types.
    Pi(RcTy<'db>, Rc<TyClosure<'db>>),

    /// Hardware arrow type: Signal => Module
    /// Non-dependent function type at the hardware level
    HArrow(RcTy<'db>, RcTy<'db>),

    // ========== The Tarski Bridge ==========
    /// El(code): Decode a type code into a semantic type
    ///
    /// This is where type codes (which are terms/values) become types.
    /// Examples:
    /// - El(UniverseCode(0)) is the type of small types
    /// - El(PiCode(A, B)) is a dependent function type
    /// - El(TypeCon(Nat, [])) is the Nat type
    El(RcValue<'db>),

    /// SignalEl(code): Decode a signal type code
    SignalEl(RcValue<'db>),

    /// ModuleEl(code): Decode a module type code
    ModuleEl(RcValue<'db>),
}

/// A type closure: produces a TYPE when applied to a VALUE
///
/// This is different from a regular `Closure` which produces a value when
/// applied to a value. A `TyClosure` is used for dependent types where the
/// codomain type depends on the domain value.
///
/// Example: In `(x : Nat) -> Vec A x`, the codomain `Vec A x` depends on
/// the value `x`, so it's represented as a `TyClosure`.
#[derive(Clone, Debug)]
pub struct TyClosure<'db> {
    /// The environment captured when the closure was created
    pub local: LocalEnv<'db>,
    /// The body is a TYPE (not a term!)
    /// When we apply this closure, we extend the environment and evaluate
    /// this type expression.
    pub body: RcTy<'db>,
}

impl<'db> TyClosure<'db> {
    pub fn new(local: LocalEnv<'db>, body: RcTy<'db>) -> Self {
        TyClosure { local, body }
    }
}

impl<'db> Ty<'db> {
    // ========== Constructors ==========

    pub fn universe_type() -> Ty<'db> {
        Ty::UniverseType
    }

    pub fn universe_type_rc() -> RcTy<'db> {
        Rc::new(Ty::UniverseType)
    }

    pub fn signal_universe_type() -> Ty<'db> {
        Ty::SignalUniverseType
    }

    pub fn signal_universe_type_rc() -> RcTy<'db> {
        Rc::new(Ty::SignalUniverseType)
    }

    pub fn module_universe_type() -> Ty<'db> {
        Ty::ModuleUniverseType
    }

    pub fn module_universe_type_rc() -> RcTy<'db> {
        Rc::new(Ty::ModuleUniverseType)
    }

    pub fn pi(source: RcTy<'db>, target: TyClosure<'db>) -> Ty<'db> {
        Ty::Pi(source, Rc::new(target))
    }

    pub fn pi_rc(source: RcTy<'db>, target: TyClosure<'db>) -> RcTy<'db> {
        Rc::new(Ty::pi(source, target))
    }

    pub fn harrow(source: RcTy<'db>, target: RcTy<'db>) -> Ty<'db> {
        Ty::HArrow(source, target)
    }

    pub fn harrow_rc(source: RcTy<'db>, target: RcTy<'db>) -> RcTy<'db> {
        Rc::new(Ty::harrow(source, target))
    }

    pub fn el(code: RcValue<'db>) -> Ty<'db> {
        Ty::El(code)
    }

    pub fn el_rc(code: RcValue<'db>) -> RcTy<'db> {
        Rc::new(Ty::el(code))
    }

    pub fn signal_el(code: RcValue<'db>) -> Ty<'db> {
        Ty::SignalEl(code)
    }

    pub fn signal_el_rc(code: RcValue<'db>) -> RcTy<'db> {
        Rc::new(Ty::signal_el(code))
    }
}
