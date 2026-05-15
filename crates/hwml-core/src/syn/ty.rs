//! Syntax-Level Type System
//!
//! This module implements syntax-level types that mirror the semantic `val::Ty`
//! types. Following the Tarski universe pattern, types are separate from terms,
//! and type codes (which are terms) are decoded into types via the `El` constructor.
//!
//! ## Architecture
//!
//! - `Ty`: Syntax-level types (unevaluated type expressions)
//! - Type codes live in `Syntax` (they are terms!)
//! - `Ty::El(code)` decodes a type code (syntax) into a type
//!
//! ## Relationship to val::Ty
//!
//! `syn::Ty` is to `val::Ty` as `Syntax` is to `Value`:
//! - `syn::Ty` uses `Binding<RcTy>` for binders (De Bruijn indices)
//! - `val::Ty` uses `TyClosure` for binders (closures with environments)
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

use crate::syn;
use crate::Binding;
use syn::RcSyntax;
use std::rc::Rc;

pub type RcTy<'db> = Rc<Ty<'db>>;
pub type BindingTy<'db> = Binding<'db, RcTy<'db>>;

/// Syntax-level types (unevaluated type expressions)
///
/// This mirrors `val::Ty` but at the syntax level. Like `val::Ty`, this
/// follows the Tarski universe pattern with El decoders.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
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
    /// The domain is a type, the codomain is a type binding.
    /// This is the syntactic representation of a dependent type.
    Pi(RcTy<'db>, BindingTy<'db>),

    /// Hardware arrow type: Signal => Module
    /// Non-dependent function type at the hardware level
    HArrow(RcTy<'db>, RcTy<'db>),

    /// Type constructor application at type level
    ///
    /// Printed as ![@Name arg1 arg2 ...]
    /// Distinguished from code form #[@Name arg1 arg2 ...]
    ///
    /// This is a native type-level representation of type constructor applications.
    /// Unlike `El(TypeConstructor(...))`, this stores type arguments as `RcTy` instead
    /// of `RcSyntax`, allowing proper type-level recursion.
    ///
    /// Examples:
    /// - ![@Nat] (Nat type)
    /// - ![@List A] (List type applied to A)
    /// - ![@Vec ![@Nat] 3] (Vec of Nat with length 3)
    TyConstructorTy(crate::val::Constant<'db>, Vec<RcTy<'db>>),

    // ========== The Tarski Bridge ==========
    /// El(code): Decode a type code into a type
    ///
    /// This is where type codes (which are terms/syntax) become types.
    /// Examples:
    /// - El(UniverseCode(0)) is the type of small types
    /// - El(PiCode(A, B)) is a dependent function type
    /// - El(TypeConstructor(Nat, [])) is the Nat type
    El(RcSyntax<'db>),

    /// SignalEl(code): Decode a signal type code
    SignalEl(RcSyntax<'db>),

    /// ModuleEl(code): Decode a module type code
    ModuleEl(RcSyntax<'db>),
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

    pub fn pi(source: RcTy<'db>, target: BindingTy<'db>) -> Ty<'db> {
        Ty::Pi(source, target)
    }

    pub fn pi_rc(source: RcTy<'db>, target: BindingTy<'db>) -> RcTy<'db> {
        Rc::new(Ty::pi(source, target))
    }

    pub fn harrow(source: RcTy<'db>, target: RcTy<'db>) -> Ty<'db> {
        Ty::HArrow(source, target)
    }

    pub fn harrow_rc(source: RcTy<'db>, target: RcTy<'db>) -> RcTy<'db> {
        Rc::new(Ty::harrow(source, target))
    }

    pub fn ty_constructor_ty(
        name: crate::val::Constant<'db>,
        args: Vec<RcTy<'db>>,
    ) -> Ty<'db> {
        Ty::TyConstructorTy(name, args)
    }

    pub fn ty_constructor_ty_rc(
        name: crate::val::Constant<'db>,
        args: Vec<RcTy<'db>>,
    ) -> RcTy<'db> {
        Rc::new(Ty::ty_constructor_ty(name, args))
    }

    pub fn el(code: RcSyntax<'db>) -> Ty<'db> {
        Ty::El(code)
    }

    pub fn el_rc(code: RcSyntax<'db>) -> RcTy<'db> {
        Rc::new(Ty::el(code))
    }

    pub fn signal_el(code: RcSyntax<'db>) -> Ty<'db> {
        Ty::SignalEl(code)
    }

    pub fn signal_el_rc(code: RcSyntax<'db>) -> RcTy<'db> {
        Rc::new(Ty::signal_el(code))
    }

    pub fn module_el(code: RcSyntax<'db>) -> Ty<'db> {
        Ty::ModuleEl(code)
    }

    pub fn module_el_rc(code: RcSyntax<'db>) -> RcTy<'db> {
        Rc::new(Ty::module_el(code))
    }

    // ========== Helper Constructors for Common Patterns ==========

    /// Create El(UniverseCode(n)) - the most common type pattern
    ///
    /// This represents the type of types at universe level n.
    /// Usage: `Ty::universe(0)` creates `El(UniverseCode(0))`
    pub fn universe(level: usize) -> RcTy<'db> {
        use crate::Syntax;
        Ty::el_rc(Rc::new(Syntax::UniverseCode(level)))
    }

    /// Create El(PiCode(...)) - dependent function type as El
    ///
    /// This wraps a PiCode term in El to create a type.
    /// Usage: `Ty::pi_code(source, icit, target)` creates `El(PiCode(source, icit, target))`
    pub fn pi_code(
        source: RcSyntax<'db>,
        icit: crate::common::Icit,
        target: syn::BindingSyntax<'db>,
    ) -> RcTy<'db> {
        use crate::Syntax;
        Ty::el_rc(Rc::new(Syntax::PiCode(source, icit, target)))
    }

    /// Create El(BitCode) - the Bit type
    ///
    /// This represents the hardware Bit type.
    /// Usage: `Ty::bit()` creates `El(BitCode)`
    pub fn bit() -> RcTy<'db> {
        use crate::Syntax;
        Ty::el_rc(Rc::new(Syntax::BitCode))
    }

    /// Create El(LiftCode(shift, inner)) - universe lifting
    ///
    /// This represents a type code lifted by n universe levels.
    /// Usage: `Ty::lift(1, code)` creates `El(LiftCode(1, code))`
    pub fn lift(shift: usize, inner: RcSyntax<'db>) -> RcTy<'db> {
        use crate::Syntax;
        Ty::el_rc(Rc::new(Syntax::LiftCode(shift, inner)))
    }
}
