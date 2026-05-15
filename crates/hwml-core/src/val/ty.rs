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
//! UniverseType : (meta-level boundary, not a type in the user's language)
//! UniverseCode(0) : UniverseType  (U₀ is a type code)
//! UniverseCode(1) : UniverseType  (U₁ is a type code)
//! Nat : El(UniverseCode(0))       (Nat is a small type)
//! Vec : El(PiCode(...))           (Vec is a type constructor)
//! El(UniverseCode(0)) : El(UniverseCode(1))  (U₀ viewed as a type lives in U₁)
//! ```

use crate::syn;
use crate::val;
use crate::{Icit, Level, MetaVariableId, QualifiedName};
use std::rc::Rc;
use val::{Closure, GlobalEnv, LocalEnv, RcValue, Spine};

pub type RcTy<'db> = Rc<Ty<'db>>;

/// Semantic types (evaluated, top-level)
///
/// **Strong Tarski Architecture**: Type codes are DECODED during evaluation.
/// Instead of wrapping codes in `El`, we decode them into structured semantic types.
///
/// Example transformations during evaluation:
/// - `El(UniverseCode(0))` → `Universe(0)` (decoded universe)
/// - `El(PiCode(A, i, B))` → `Pi(A_ty, i, B_closure)` (decoded Pi)
/// - `El(BitCode)` → `BitType` (decoded Bit)
/// - `El(Rigid var)` → `RigidTy(var, ...)` (neutral type)
#[derive(Clone, Debug)]
pub enum Ty<'db> {
    // ========== Universe Types (The Meta-Classifiers) ==========
    /// The absolute meta-level ceiling for standard universes.
    ///
    /// This classifies universe codes: `UniverseCode(0) : UniverseType`, `UniverseCode(1) : UniverseType`, etc.
    UniverseType,

    /// The type of signal types - classifies signal universe codes.
    /// This is the meta-level classifier for the signal universe hierarchy.
    SignalUniverseType,

    /// The type of module types - classifies module universe codes.
    /// This is the meta-level classifier for the module universe hierarchy.
    ModuleUniverseType,

    // ========== Top-Level Type Formers ==========
    /// Dependent function type: (x : A) -> B
    ///
    /// **UPDATED for Strong Tarski**: Now includes `Icit` to unify native meta-level
    /// arrows and decoded object-level PiCode. This is the single representation for
    /// all function types.
    ///
    /// The domain is a type, the codomain is a TYPE CLOSURE that depends on
    /// a VALUE (not a type!). This is the key to dependent types.
    Pi(RcTy<'db>, Icit, Rc<TyClosure<'db>>),

    /// Hardware arrow type: Signal => Module
    /// Non-dependent function type at the hardware level
    HArrow(RcTy<'db>, RcTy<'db>),

    // ========== Strong Tarski: Decoded Type Codes ==========
    /// Decoded universe: `El(UniverseCode(n))` becomes `Universe(n)`
    ///
    /// This is a universe at level `n`. Small types live in `Universe(0)`,
    /// and we have `Universe(n) : Universe(n+1)` for stratification.
    Universe(usize),

    /// Decoded Bit type: `El(BitCode)` becomes `BitType`
    ///
    /// The primitive hardware bit type.
    BitType,

    /// Decoded Lift: `El(LiftCode(n, inner))` becomes `LiftType(n, inner_ty)`
    ///
    /// Universe lifting for cumulativity. Lifts a type from universe `k` to `k+n`.
    LiftType(usize, RcTy<'db>),

    /// Decoded type constructor: `El(TypeConstructor(name, args))` becomes `TyConstructor(name, args_tys)`
    ///
    /// A user-defined type constructor applied to type arguments.
    /// Example: `Vec : Type → Nat → Type`, so `Vec Bit 5` has args `[Bit, 5]` (both terms!)
    TyConstructor(QualifiedName<'db>, Vec<RcValue<'db>>),

    // ========== Neutral Types (Stuck/Unknown Types) ==========
    /// Rigid neutral type: `El(Rigid var)` becomes `RigidTy`
    ///
    /// **CRITICAL**: The spine contains TERM-LEVEL arguments (RcValue), not types!
    /// A type variable applied to arguments receives terms, not types.
    ///
    /// Example: `Vec Bit 5` where `Vec` is a type variable
    /// - Head: `Vec` (type variable at some level)
    /// - Spine: `[Application(Bit), Application(5)]` where both are VALUES
    /// - Type: The type of this stuck type application
    RigidTy(TyVariable, Spine<'db>, RcTy<'db>),

    /// Flex neutral type: `El(Flex meta)` becomes `FlexTy`
    ///
    /// **CRITICAL**: The spine contains TERM-LEVEL arguments (RcValue), not types!
    /// A type metavariable applied to arguments.
    FlexTy(TyMetaVariable<'db>, Spine<'db>, RcTy<'db>),

    // ========== Signal and Module Domains (Embedded Type Systems) ==========
    /// SignalEl(value): Wrap a Signal domain value as a type
    ///
    /// **IMPORTANT**: Signal values (Bit, Zero, One) are NOT type codes.
    /// They are values in the Signal domain that act as types.
    /// This variant embeds the Signal type system into the standard type system.
    SignalEl(RcValue<'db>),

    /// ModuleEl(value): Wrap a Module domain value as a type
    ///
    /// **IMPORTANT**: Module values (HArrow, Module) are NOT type codes.
    /// They are values in the Module domain that act as types.
    /// This variant embeds the Module type system into the standard type system.
    ModuleEl(RcValue<'db>),
}

/// Type-level variable (for neutral types)
///
/// Mirrors `Variable` but at the type level. Used in `RigidTy` to represent
/// a type variable that is stuck (cannot reduce further).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TyVariable {
    pub level: Level,
}

impl TyVariable {
    pub fn new(level: Level) -> Self {
        TyVariable { level }
    }
}

/// Type-level metavariable (for neutral types)
///
/// Mirrors `MetaVariable` but at the type level. Used in `FlexTy` to represent
/// a type metavariable that may be solved later.
#[derive(Clone, Debug)]
pub struct TyMetaVariable<'db> {
    pub id: MetaVariableId,
    pub local: LocalEnv<'db>,
}

impl<'db> TyMetaVariable<'db> {
    pub fn new(id: MetaVariableId, local: LocalEnv<'db>) -> Self {
        TyMetaVariable { id, local }
    }
}

/// A type closure: produces a TYPE when applied to a VALUE
///
/// This is different from a regular `Closure` which produces a value when
/// applied to a value. A `TyClosure` is used for dependent types where the
/// codomain type depends on the domain value.
///
/// Example: In `(x : Nat) -> Vec A x`, the codomain `Vec A x` depends on
/// the value `x`, so it's represented as a `TyClosure`.
///
/// **Strong Tarski**: TyClosure can be either:
/// - `Syntactic`: From `syn::Ty::Pi` - stores syntactic body
/// - `Decoding`: From decoded `PiCode` - wraps value closure and decodes result
#[derive(Clone, Debug)]
pub enum TyClosure<'db> {
    /// Syntactic type closure (from syn::Ty::Pi)
    ///
    /// The body is SYNTACTIC (syn::RcTy) with one free De Bruijn variable.
    /// When applied, we evaluate the body in an extended environment.
    Syntactic {
        local: LocalEnv<'db>,
        body: syn::RcTy<'db>,
    },

    /// Decoding type closure (from decoded PiCode)
    ///
    /// Wraps a value closure that produces type codes.
    /// When applied, we run the value closure and decode the result.
    Decoding {
        global: GlobalEnv<'db>,
        value_closure: Closure<'db>,
    },
}

impl<'db> TyClosure<'db> {
    pub fn new(local: LocalEnv<'db>, body: syn::RcTy<'db>) -> Self {
        TyClosure::Syntactic { local, body }
    }

    pub fn new_decoding(global: GlobalEnv<'db>, value_closure: Closure<'db>) -> Self {
        TyClosure::Decoding {
            global,
            value_closure,
        }
    }
}

/// Run a type closure with arguments.
///
/// **Strong Tarski**: Handles both Syntactic and Decoding closures.
///
/// - Syntactic: Evaluates syntactic body in extended environment
/// - Decoding: Applies value closure and decodes the result
pub fn run_ty_closure<'db, 'g, T>(
    global: &'g GlobalEnv<'db>,
    closure: &TyClosure<'db>,
    args: T,
) -> Result<RcTy<'db>, crate::eval::Error<'db>>
where
    T: IntoIterator<Item = RcValue<'db>>,
{
    match closure {
        TyClosure::Syntactic { local, body } => {
            // 1. Start with the captured environment
            let mut local = local.clone();

            // 2. Extend with the arguments (binds the free variable in the body)
            for arg in args {
                local.push(arg);
            }

            // 3. Create an evaluation environment
            let mut env = val::Environment {
                global,
                local,
                transparent: val::TransparentEnv::new(),
            };

            // 4. Evaluate the syntactic body to get the semantic type
            crate::eval::eval_ty(&mut env, body)
        }

        TyClosure::Decoding {
            global: closure_global,
            value_closure,
        } => {
            // Apply the value closure to each argument and decode the final result
            let args_vec: Vec<_> = args.into_iter().collect();

            if args_vec.is_empty() {
                // No arguments, just evaluate the closure body
                let type_code = crate::eval::run_closure(closure_global, value_closure, [])?;
                crate::eval::decode_type_code(closure_global, &type_code)
            } else {
                // Apply arguments one by one
                let type_code = crate::eval::run_closure(closure_global, value_closure, args_vec)?;
                crate::eval::decode_type_code(closure_global, &type_code)
            }
        }
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

    pub fn pi(source: RcTy<'db>, icit: Icit, target: TyClosure<'db>) -> Ty<'db> {
        Ty::Pi(source, icit, Rc::new(target))
    }

    pub fn pi_rc(source: RcTy<'db>, icit: Icit, target: TyClosure<'db>) -> RcTy<'db> {
        Rc::new(Ty::pi(source, icit, target))
    }

    pub fn harrow(source: RcTy<'db>, target: RcTy<'db>) -> Ty<'db> {
        Ty::HArrow(source, target)
    }

    pub fn harrow_rc(source: RcTy<'db>, target: RcTy<'db>) -> RcTy<'db> {
        Rc::new(Ty::harrow(source, target))
    }

    // **PHASE 9**: Deleted `el()` and `el_rc()` - use decoded types instead!
    // Standard type codes are now decoded into:
    // - Universe(n), Pi(...), BitType, LiftType, TyConstructor, RigidTy, FlexTy

    pub fn signal_el(code: RcValue<'db>) -> Ty<'db> {
        Ty::SignalEl(code)
    }

    pub fn signal_el_rc(code: RcValue<'db>) -> RcTy<'db> {
        Rc::new(Ty::signal_el(code))
    }

    pub fn module_el(code: RcValue<'db>) -> Ty<'db> {
        Ty::ModuleEl(code)
    }

    pub fn module_el_rc(code: RcValue<'db>) -> RcTy<'db> {
        Rc::new(Ty::module_el(code))
    }

    // ========== Strong Tarski Constructors ==========

    pub fn universe(level: usize) -> Ty<'db> {
        Ty::Universe(level)
    }

    pub fn universe_rc(level: usize) -> RcTy<'db> {
        Rc::new(Ty::universe(level))
    }

    pub fn bit_type() -> Ty<'db> {
        Ty::BitType
    }

    pub fn bit_type_rc() -> RcTy<'db> {
        Rc::new(Ty::BitType)
    }

    pub fn lift_type(shift: usize, inner: RcTy<'db>) -> Ty<'db> {
        Ty::LiftType(shift, inner)
    }

    pub fn lift_type_rc(shift: usize, inner: RcTy<'db>) -> RcTy<'db> {
        Rc::new(Ty::lift_type(shift, inner))
    }

    pub fn ty_constructor(name: QualifiedName<'db>, args: Vec<RcValue<'db>>) -> Ty<'db> {
        Ty::TyConstructor(name, args)
    }

    pub fn ty_constructor_rc(name: QualifiedName<'db>, args: Vec<RcValue<'db>>) -> RcTy<'db> {
        Rc::new(Ty::ty_constructor(name, args))
    }

    pub fn rigid_ty(var: TyVariable, spine: Spine<'db>, ty: RcTy<'db>) -> Ty<'db> {
        Ty::RigidTy(var, spine, ty)
    }

    pub fn rigid_ty_rc(var: TyVariable, spine: Spine<'db>, ty: RcTy<'db>) -> RcTy<'db> {
        Rc::new(Ty::rigid_ty(var, spine, ty))
    }

    pub fn flex_ty(meta: TyMetaVariable<'db>, spine: Spine<'db>, ty: RcTy<'db>) -> Ty<'db> {
        Ty::FlexTy(meta, spine, ty)
    }

    pub fn flex_ty_rc(meta: TyMetaVariable<'db>, spine: Spine<'db>, ty: RcTy<'db>) -> RcTy<'db> {
        Rc::new(Ty::flex_ty(meta, spine, ty))
    }
}
