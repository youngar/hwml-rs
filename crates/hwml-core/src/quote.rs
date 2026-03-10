//! Quotation: converting semantic Values back to syntactic Syntax.
//!
//! This module implements type-directed quotation (readback) from the semantic
//! domain to the syntactic domain. The structure mirrors equal.rs:
//! - `quote` is the main entry point that dispatches based on type
//! - `quote_*_instances` handle quoting instances of specific types
//! - `quote_*` handle quoting specific term constructors

#![allow(unused_imports)]

use crate::{
    common::{Level, Location},
    eval::{self, eval_telescope, run_closure},
    syn::{CaseBranch, RcSyntax, Syntax},
    val::{
        self, Closure, Eliminator, Environment, Flex, GlobalEnv, HArrow, LocalEnv, Module, Normal,
        Pi, Rigid, TransparentEnv, TypeConstructor,
    },
    ConstantId, UniverseLevel, Value,
};
use std::rc::Rc;

/// A quotation error.
#[derive(Debug, Clone)]
pub enum Error<'db> {
    /// Something about the input was ill-typed, preventing quotation.
    IllTyped,
    /// Quotation can force evaluation, which may itself error.
    EvalError(eval::Error),
    LookupError(val::LookupError<'db>),
}

impl<'db> From<eval::Error> for Error<'db> {
    fn from(error: eval::Error) -> Self {
        Error::EvalError(error)
    }
}

impl<'db> From<val::LookupError<'db>> for Error<'db> {
    fn from(error: val::LookupError<'db>) -> Self {
        Error::LookupError(error)
    }
}

type Result<'db, T> = std::result::Result<T, Error<'db>>;

// ============================================================================
// Main Entry Points
// ============================================================================

/// Read a normal (value * type) back into syntax.
pub fn quote_normal<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    normal: &Normal<'db>,
) -> Result<'db, RcSyntax<'db>> {
    quote(global, depth, &normal.value, &normal.ty)
}

/// Read a value back into syntax at a given type.
/// Quotation is type-directed: we dispatch based on the type.
pub fn quote<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    ty: &Value<'db>,
) -> Result<'db, RcSyntax<'db>> {
    if let Value::Let(let_val) = value {
        return quote_let(global, depth, let_val, ty);
    }

    match ty {
        Value::Universe(universe) => quote_universe_instances(global, depth, value, universe),
        Value::Lift(lift) => quote_lift_instances(global, depth, value, lift),
        Value::Pi(pi) => quote_pi_instances(global, depth, value, pi),
        Value::TypeConstructor(tcon) => {
            quote_type_constructor_instances(global, depth, value, tcon)
        }
        Value::HardwareUniverse(hwuniverse) => {
            quote_hwuniverse_instances(global, depth, value, hwuniverse)
        }
        Value::SignalUniverse(signal_universe) => {
            quote_signal_universe_instances(global, depth, value, signal_universe)
        }
        Value::ModuleUniverse(module_universe) => {
            quote_module_universe_instances(global, depth, value, module_universe)
        }
        // Hardware-level types
        Value::SLift(slift) => quote_slift_instances(global, depth, value, slift),
        Value::MLift(mlift) => quote_mlift_instances(global, depth, value, mlift),
        Value::Bit(bit) => quote_bit_instances(global, depth, value, bit),
        Value::HArrow(harrow) => quote_harrow_instances(global, depth, value, harrow),
        // Neutral types
        Value::Prim(prim) => quote_prim_instances(global, depth, value, prim),
        Value::Constant(constant) => quote_constant_instances(global, depth, value, constant),
        Value::Rigid(rigid) => quote_rigid_instances(global, depth, value, rigid),
        Value::Flex(flex) => quote_flex_instances(global, depth, value, flex),
        // Equality types
        Value::EqType(eq) => quote_eq_instances(global, depth, value, eq),
        _ => Err(Error::IllTyped),
    }
}
// ============================================================================
// Instance Quotation Functions
// ============================================================================

/// Quote an instance of a Universe (i.e., a type).
pub fn quote_universe_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    _universe: &val::Universe<'db>,
) -> Result<'db, RcSyntax<'db>> {
    type_quote(global, depth, value)
}

/// Quote an instance of a Lift type.
pub fn quote_lift_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    lift: &val::Lift<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match lift.ty.as_ref() {
        Value::SLift(slift) => quote_slift_instances(global, depth, value, slift),
        Value::MLift(mlift) => quote_mlift_instances(global, depth, value, mlift),
        _ => Err(Error::IllTyped),
    }
}

/// Quote an instance of a Pi type.
/// Neutrals are eta-expanded: a neutral `f` becomes `λx. f x`.
pub fn quote_pi_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    pi: &Pi<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::Lambda(lambda) => quote_lambda(global, depth, lambda, pi),
        // For neutrals, eta-expand by applying to a fresh variable
        Value::Prim(_) | Value::Constant(_) | Value::Rigid(_) | Value::Flex(_) => {
            eta_expand_pi(global, depth, value, pi)
        }
        _ => Err(Error::IllTyped),
    }
}

/// Eta-expand a value at a Pi type.
/// Creates a lambda that applies the value to a fresh variable.
fn eta_expand_pi<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    pi: &Pi<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Create a fresh variable of the source type
    let arg = Rc::new(Value::variable(Level::new(depth), pi.source.clone()));

    // Apply the value to the fresh variable
    let applied = eval::run_application(global, value, arg.clone())?;

    // Get the result type
    let result_ty = run_closure(global, &pi.target, [arg])?;

    // Quote the result at the target type
    let syn_body = quote(global, depth + 1, &applied, &result_ty)?;

    Ok(Syntax::lambda_rc(Location::UNKNOWN, syn_body))
}

/// Quote an instance of a TypeConstructor.
pub fn quote_type_constructor_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    tcon: &TypeConstructor<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::DataConstructor(dcon) => quote_data_constructor(global, depth, dcon, tcon),
        Value::Prim(prim) => quote_prim(global, depth, prim),
        Value::Constant(constant) => quote_constant(global, depth, constant),
        Value::Rigid(rigid) => quote_rigid(global, depth, rigid),
        Value::Flex(flex) => quote_flex(global, depth, flex),
        _ => Err(Error::IllTyped),
    }
}

/// Quote an instance of HardwareUniverse (a hardware type).
/// HardwareUniverse has two constructors: SLift and MLift.
pub fn quote_hwuniverse_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    _hwuniverse: &val::HardwareUniverse<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::SLift(slift) => quote_slift(global, depth, slift),
        Value::MLift(mlift) => quote_mlift(global, depth, mlift),
        Value::Prim(prim) => quote_prim(global, depth, prim),
        Value::Constant(constant) => quote_constant(global, depth, constant),
        Value::Rigid(rigid) => quote_rigid(global, depth, rigid),
        Value::Flex(flex) => quote_flex(global, depth, flex),
        _ => Err(Error::IllTyped),
    }
}

/// Quote an instance of an SLift type (lifted signal type).
pub fn quote_slift_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    slift: &val::SLift<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // SLift's ty should be a signal type (like Bit)
    match slift.ty.as_ref() {
        Value::Bit(bit) => quote_bit_instances(global, depth, value, bit),
        _ => Err(Error::IllTyped),
    }
}

/// Quote an instance of an MLift type (lifted module type).
pub fn quote_mlift_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    mlift: &val::MLift<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // MLift's ty should be a module type (like HArrow)
    match mlift.ty.as_ref() {
        Value::HArrow(harrow) => quote_harrow_instances(global, depth, value, harrow),
        _ => Err(Error::IllTyped),
    }
}

/// Quote an instance of an HArrow type (hardware function type).
pub fn quote_harrow_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    harrow: &HArrow<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::Module(module) => quote_module(global, depth, module, harrow),
        Value::Prim(prim) => quote_prim(global, depth, prim),
        Value::Constant(constant) => quote_constant(global, depth, constant),
        Value::Rigid(rigid) => quote_rigid(global, depth, rigid),
        Value::Flex(flex) => quote_flex(global, depth, flex),
        _ => Err(Error::IllTyped),
    }
}

/// Quote an instance of Bit type.
pub fn quote_bit_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    _bit: &val::Bit<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::Zero(_) => Ok(Syntax::zero_rc(Location::UNKNOWN)),
        Value::One(_) => Ok(Syntax::one_rc(Location::UNKNOWN)),
        Value::Prim(prim) => quote_prim(global, depth, prim),
        Value::Constant(constant) => quote_constant(global, depth, constant),
        Value::Rigid(rigid) => quote_rigid(global, depth, rigid),
        Value::Flex(flex) => quote_flex(global, depth, flex),
        Value::HApplication(happ) => quote_happlication(global, depth, happ),
        _ => Err(Error::IllTyped),
    }
}

/// Quote an HApplication (hardware application).
/// An HApplication is `m<T>(x)` where m is a module, T is its domain type, and x is the argument.
pub fn quote_happlication<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    happ: &val::HApplication<'db>,
) -> Result<'db, RcSyntax<'db>> {
    let module = quote(global, depth, &happ.module, &happ.module_ty)?;
    let domain_ty = match happ.module_ty.as_ref() {
        Value::HArrow(harrow) => type_quote(global, depth, &harrow.source)?,
        _ => return Err(Error::IllTyped),
    };
    let argument = quote(
        global,
        depth,
        &happ.argument,
        match happ.module_ty.as_ref() {
            Value::HArrow(harrow) => harrow.source.as_ref(),
            _ => return Err(Error::IllTyped),
        },
    )?;
    Ok(Syntax::happlication_rc(
        Location::UNKNOWN,
        module,
        domain_ty,
        argument,
    ))
}

/// Quote an instance of SignalUniverse (a signal type).
pub fn quote_signal_universe_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    _signal_universe: &val::SignalUniverse<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::Bit(bit) => quote_bit(global, depth, bit),
        Value::Prim(prim) => quote_prim(global, depth, prim),
        Value::Constant(constant) => quote_constant(global, depth, constant),
        Value::Rigid(rigid) => quote_rigid(global, depth, rigid),
        Value::Flex(flex) => quote_flex(global, depth, flex),
        _ => Err(Error::IllTyped),
    }
}

/// Quote an instance of ModuleUniverse (a module type).
pub fn quote_module_universe_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    _module_universe: &val::ModuleUniverse<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::HArrow(harrow) => quote_harrow(global, depth, harrow),
        Value::Prim(prim) => quote_prim(global, depth, prim),
        Value::Constant(constant) => quote_constant(global, depth, constant),
        Value::Rigid(rigid) => quote_rigid(global, depth, rigid),
        Value::Flex(flex) => quote_flex(global, depth, flex),
        _ => Err(Error::IllTyped),
    }
}

/// Quote an instance of a Prim type.
pub fn quote_prim_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    _prim: &ConstantId<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::Prim(prim) => quote_prim(global, depth, prim),
        Value::Constant(constant) => quote_constant(global, depth, constant),
        Value::Rigid(rigid) => quote_rigid(global, depth, rigid),
        Value::Flex(flex) => quote_flex(global, depth, flex),
        _ => Err(Error::IllTyped),
    }
}

/// Quote an instance of a Constant type.
pub fn quote_constant_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    _constant: &ConstantId<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::Prim(prim) => quote_prim(global, depth, prim),
        Value::Constant(constant) => quote_constant(global, depth, constant),
        Value::Rigid(rigid) => quote_rigid(global, depth, rigid),
        Value::Flex(flex) => quote_flex(global, depth, flex),
        _ => Err(Error::IllTyped),
    }
}

/// Quote an instance of a Rigid type.
pub fn quote_rigid_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    _rigid: &Rigid<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::Prim(prim) => quote_prim(global, depth, prim),
        Value::Constant(constant) => quote_constant(global, depth, constant),
        Value::Rigid(rigid) => quote_rigid(global, depth, rigid),
        Value::Flex(flex) => quote_flex(global, depth, flex),
        _ => Err(Error::IllTyped),
    }
}

/// Quote an instance of a Flex type.
pub fn quote_flex_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    _flex: &Flex<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::Prim(prim) => quote_prim(global, depth, prim),
        Value::Constant(constant) => quote_constant(global, depth, constant),
        Value::Rigid(rigid) => quote_rigid(global, depth, rigid),
        Value::Flex(flex) => quote_flex(global, depth, flex),
        _ => Err(Error::IllTyped),
    }
}
// ============================================================================
// Structural Quotation Functions
// ============================================================================

/// Read back a type (a value that is itself a type) into syntax.
pub fn type_quote<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::Universe(universe) => quote_universe(global, depth, universe),
        Value::Lift(lift) => quote_lift(global, depth, lift),
        Value::Pi(pi) => quote_pi(global, depth, pi),
        Value::TypeConstructor(tcon) => quote_type_constructor(global, depth, tcon),
        Value::HardwareUniverse(hwuniverse) => quote_hardware_universe(global, depth, hwuniverse),
        Value::SLift(slift) => quote_slift(global, depth, slift),
        Value::MLift(mlift) => quote_mlift(global, depth, mlift),
        Value::SignalUniverse(signal_universe) => {
            quote_signal_universe(global, depth, signal_universe)
        }
        Value::ModuleUniverse(module_universe) => {
            quote_module_universe(global, depth, module_universe)
        }
        Value::Bit(bit) => quote_bit(global, depth, bit),
        Value::HArrow(harrow) => quote_harrow(global, depth, harrow),
        Value::Prim(prim) => quote_prim(global, depth, prim),
        Value::Constant(constant) => quote_constant(global, depth, constant),
        Value::Rigid(rigid) => quote_rigid(global, depth, rigid),
        Value::Flex(flex) => quote_flex(global, depth, flex),
        Value::EqType(eq) => quote_eq_type(global, depth, eq),
        _ => Err(Error::IllTyped),
    }
}
/// Quote a Universe to syntax.
pub fn quote_universe<'db>(
    _global: &GlobalEnv<'db>,
    _depth: usize,
    universe: &val::Universe<'db>,
) -> Result<'db, RcSyntax<'db>> {
    Ok(Syntax::universe_rc(Location::UNKNOWN, universe.level))
}

/// Quote a Lift type to syntax.
pub fn quote_lift<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lift: &val::Lift<'db>,
) -> Result<'db, RcSyntax<'db>> {
    let ty = type_quote(global, depth, &lift.ty)?;
    Ok(Syntax::lift_rc(Location::UNKNOWN, ty))
}

/// Quote a Pi type to syntax.
pub fn quote_pi<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    pi: &Pi<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Quote the source type
    let syn_source = type_quote(global, depth, &pi.source)?;

    // Create a fresh variable for the binder
    let arg = Rc::new(Value::variable(Level::new(depth), pi.source.clone()));
    let sem_target = run_closure(global, &pi.target, [arg])?;
    let syn_target = type_quote(global, depth + 1, &sem_target)?;

    Ok(Syntax::pi_rc(Location::UNKNOWN, syn_source, syn_target))
}

/// Quote a Lambda to syntax, using its Pi type.
pub fn quote_lambda<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lambda: &val::Lambda<'db>,
    pi: &Pi<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Create a fresh variable for the binder
    let arg = Rc::new(Value::variable(Level::new(depth), pi.source.clone()));

    // Get the result type and body value
    let result_ty = run_closure(global, &pi.target, [arg.clone()])?;
    let body_val = run_closure(global, &lambda.body, [arg])?;

    // Quote the body at the result type
    let syn_body = quote(global, depth + 1, &body_val, &result_ty)?;

    Ok(Syntax::lambda_rc(Location::UNKNOWN, syn_body))
}

pub fn quote_let<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    let_val: &val::Let<'db>,
    _expected_ty: &Value<'db>,
) -> Result<'db, RcSyntax<'db>> {
    let syn_ty = quote_at_unknown_type(global, depth, &let_val.ty)?;
    let syn_value = quote(global, depth, &let_val.value, &let_val.ty)?;
    let syn_body = quote(global, depth + 1, &let_val.body, _expected_ty)?;
    Ok(Syntax::let_rc(
        Location::UNKNOWN,
        syn_ty,
        syn_value,
        syn_body,
    ))
}

fn quote_at_unknown_type<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
) -> Result<'db, RcSyntax<'db>> {
    type_quote(global, depth, value)
}

/// Quote a TypeConstructor to syntax.
pub fn quote_type_constructor<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    tcon: &TypeConstructor<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Look up the type info
    let type_info = global
        .type_constructor(tcon.constructor)
        .map_err(Error::LookupError)?
        .clone();

    // Create an environment for evaluating argument types
    let mut env = Environment {
        global,
        local: LocalEnv::new(),
        transparent: TransparentEnv::new(),
    };

    // Quote each argument (parameters and indices)
    let mut arguments = Vec::new();
    for (sem_arg, syn_ty) in tcon.iter().zip(type_info.arguments.iter()) {
        let sem_ty = eval::eval(&mut env, &syn_ty)?;
        let syn_arg = quote(global, depth, sem_arg, &sem_ty)?;
        arguments.push(syn_arg);
        env.push(sem_arg.clone());
    }

    Ok(Syntax::type_constructor_rc(
        Location::UNKNOWN,
        tcon.constructor,
        arguments,
    ))
}

/// Quote a DataConstructor to syntax.
pub fn quote_data_constructor<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    dcon: &val::DataConstructor<'db>,
    tcon: &TypeConstructor<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Look up the type and data constructor info
    let type_info = global
        .type_constructor(tcon.constructor)
        .map_err(Error::LookupError)?
        .clone();
    let data_info = global
        .data_constructor(dcon.constructor)
        .map_err(Error::LookupError)?
        .clone();

    // Get number of parameters
    let num_parameters = type_info.num_parameters();

    // Create environment with parameters
    let parameters = tcon.iter().take(num_parameters).cloned();
    let mut env = Environment {
        global,
        local: LocalEnv::new(),
        transparent: TransparentEnv::new(),
    };
    env.extend(parameters);

    // Quote each argument
    let mut arguments = Vec::new();
    for (sem_arg, syn_ty) in dcon.iter().zip(data_info.arguments.bindings.iter()) {
        let sem_ty = eval::eval(&mut env, syn_ty)?;
        let syn_arg = quote(global, depth, sem_arg, &sem_ty)?;
        arguments.push(syn_arg);
        env.push(sem_arg.clone());
    }

    Ok(Syntax::data_constructor_rc(
        Location::UNKNOWN,
        dcon.constructor,
        arguments,
    ))
}

/// Quote HardwareUniverse to syntax.
pub fn quote_hardware_universe<'db>(
    _global: &GlobalEnv<'db>,
    _depth: usize,
    _hwuniverse: &val::HardwareUniverse<'db>,
) -> Result<'db, RcSyntax<'db>> {
    Ok(Syntax::hardware_rc(Location::UNKNOWN))
}

/// Quote SLift to syntax.
pub fn quote_slift<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    slift: &val::SLift<'db>,
) -> Result<'db, RcSyntax<'db>> {
    let ty = type_quote(global, depth, &slift.ty)?;
    Ok(Syntax::slift_rc(Location::UNKNOWN, ty))
}

/// Quote MLift to syntax.
pub fn quote_mlift<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    mlift: &val::MLift<'db>,
) -> Result<'db, RcSyntax<'db>> {
    let ty = type_quote(global, depth, &mlift.ty)?;
    Ok(Syntax::mlift_rc(Location::UNKNOWN, ty))
}

/// Quote SignalUniverse to syntax.
pub fn quote_signal_universe<'db>(
    _global: &GlobalEnv<'db>,
    _depth: usize,
    _signal_universe: &val::SignalUniverse<'db>,
) -> Result<'db, RcSyntax<'db>> {
    Ok(Syntax::signal_universe_rc(Location::UNKNOWN))
}

/// Quote ModuleUniverse to syntax.
pub fn quote_module_universe<'db>(
    _global: &GlobalEnv<'db>,
    _depth: usize,
    _module_universe: &val::ModuleUniverse<'db>,
) -> Result<'db, RcSyntax<'db>> {
    Ok(Syntax::module_universe_rc(Location::UNKNOWN))
}

/// Quote Bit type to syntax.
pub fn quote_bit<'db>(
    _global: &GlobalEnv<'db>,
    _depth: usize,
    _bit: &val::Bit<'db>,
) -> Result<'db, RcSyntax<'db>> {
    Ok(Syntax::bit_rc(Location::UNKNOWN))
}

/// Quote HArrow to syntax.
pub fn quote_harrow<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    harrow: &HArrow<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Quote the source type
    let syn_source = type_quote(global, depth, &harrow.source)?;

    // Create a fresh variable for the binder
    let arg = Rc::new(Value::variable(Level::new(depth), harrow.source.clone()));
    let sem_target = run_closure(global, &harrow.target, [arg])?;
    let syn_target = type_quote(global, depth + 1, &sem_target)?;

    Ok(Syntax::harrow_rc(
        Location::UNKNOWN,
        syn_source,
        syn_target,
    ))
}

/// Quote a Module to syntax, using its HArrow type.
pub fn quote_module<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    module: &Module<'db>,
    harrow: &HArrow<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Create a fresh variable for the binder
    let arg = Rc::new(Value::variable(Level::new(depth), harrow.source.clone()));

    // Get the result type and body value
    let result_ty = run_closure(global, &harrow.target, [arg.clone()])?;
    let body_val = run_closure(global, &module.body, [arg])?;

    // Quote the body at the result type
    let syn_body = quote(global, depth + 1, &body_val, &result_ty)?;

    Ok(Syntax::module_rc(Location::UNKNOWN, syn_body))
}
// ============================================================================
// Neutral Quotation Functions
// ============================================================================

/// Quote a Prim to syntax.
pub fn quote_prim<'db>(
    _global: &GlobalEnv<'db>,
    _depth: usize,
    prim: &ConstantId<'db>,
) -> Result<'db, RcSyntax<'db>> {
    Ok(Syntax::prim_rc(Location::UNKNOWN, *prim))
}

/// Quote a Constant to syntax.
pub fn quote_constant<'db>(
    _global: &GlobalEnv<'db>,
    _depth: usize,
    constant: &ConstantId<'db>,
) -> Result<'db, RcSyntax<'db>> {
    Ok(Syntax::constant_rc(Location::UNKNOWN, *constant))
}

/// Quote a Rigid neutral to syntax.
pub fn quote_rigid<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    rigid: &Rigid<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Start with the variable head
    let mut result = quote_variable(depth, &rigid.head);

    // Apply each eliminator in the spine
    for eliminator in rigid.spine.iter() {
        result = quote_eliminator(global, depth, result, eliminator)?;
    }

    Ok(result)
}

/// Quote a Flex neutral to syntax.
pub fn quote_flex<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    flex: &Flex<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Start with the metavariable head
    let mut result = quote_metavariable(global, depth, &flex.head)?;

    // Apply each eliminator in the spine
    for eliminator in flex.spine.iter() {
        result = quote_eliminator(global, depth, result, eliminator)?;
    }

    Ok(result)
}

/// Quote a variable to syntax.
fn quote_variable<'db>(depth: usize, var: &val::Variable) -> RcSyntax<'db> {
    Syntax::variable_rc(Location::UNKNOWN, var.level.to_index(depth))
}

/// Quote a metavariable to syntax.
fn quote_metavariable<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    meta: &val::MetaVariable<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Look up metavariable info for argument types
    let meta_info = global.metavariable(meta.id).map_err(|_| Error::IllTyped)?;

    // Create environment for evaluating argument types
    let mut env = Environment {
        global,
        local: LocalEnv::new(),
        transparent: TransparentEnv::new(),
    };

    // Quote each value in the local environment
    let mut substitution = Vec::new();
    for (value, syn_ty) in meta.local.iter().zip(meta_info.arguments.iter()) {
        let sem_ty = eval::eval(&mut env, syn_ty)?;
        let quoted = quote(global, depth, value.as_ref(), &sem_ty)?;
        substitution.push(quoted);
        env.push(value.clone());
    }

    Ok(Syntax::metavariable_rc(
        Location::UNKNOWN,
        meta.id,
        substitution,
    ))
}

/// Quote an eliminator applied to a head term.
fn quote_eliminator<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    head: RcSyntax<'db>,
    eliminator: &Eliminator<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match eliminator {
        Eliminator::Application(app) => {
            let syn_arg = quote_normal(global, depth, &app.argument)?;
            Ok(Syntax::application_rc(Location::UNKNOWN, head, syn_arg))
        }
        Eliminator::Case(case) => quote_case_eliminator(global, depth, head, case),
    }
}
// ============================================================================
// Case Quotation
// ============================================================================

/// Quote a stuck case expression to syntax.
///
/// Since we use a simple return type (not a motive), the return type is the same
/// for all branches and doesn't depend on the scrutinee.
fn quote_case_eliminator<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    syn_scrutinee: RcSyntax<'db>,
    sem_case: &val::Case<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // The scrutinee must be a variable (not an arbitrary expression).
    // The `syn_scrutinee` is the quoted head of the neutral term, which should
    // always be a Variable. Extract the Variable struct for the Case syntax.
    use crate::syn::SyntaxData;
    let scrutinee_var = match &syn_scrutinee.data {
        SyntaxData::Variable(var) => var.clone(),
        _ => return Err(Error::IllTyped), // Case scrutinee must be a variable
    };

    let _type_info = global.type_constructor(sem_case.type_constructor)?;

    let parameters = &sem_case.parameters;

    // No return_type in case anymore - case is check-only.
    // For quoting branch bodies, we use a placeholder type.
    // TODO: Thread the expected type through when we have check-only quoting.
    let placeholder_ty = Rc::new(Value::Universe(val::Universe::new(UniverseLevel::new(0))));

    let mut branches = Vec::new();
    for branch in &sem_case.branches {
        let data_info = global.data_constructor(branch.constructor)?;

        // Create an instance of this data constructor to evaluate the branch body
        let dcon_arg_tys = eval_telescope(global, parameters.clone(), &data_info.arguments)?;
        let mut dcon_args = Vec::new();
        for ty in dcon_arg_tys.types {
            dcon_args.push(Rc::new(Value::variable(
                Level::new(depth + dcon_args.len()),
                ty,
            )));
        }

        // Evaluate the branch body closure
        let branch_val = run_closure(global, &branch.body, dcon_args)?;
        let branch_syn = quote(global, depth + branch.arity, &branch_val, &placeholder_ty)?;
        branches.push(CaseBranch::new(
            branch.constructor,
            branch.arity,
            branch_syn,
        ));
    }

    // No return_type to quote - case expressions are check-only
    Ok(Syntax::case_rc(
        Location::UNKNOWN,
        scrutinee_var.index,
        branches,
    ))
}

// ============================================================================
// Equality Type Quotation
// ============================================================================

/// Quote an instance of an equality type.
/// At type `Eq A x y`, the instance is a proof of equality.
pub fn quote_eq_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    eq: &val::EqType<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::Refl(_) => Ok(Syntax::refl_rc(Location::UNKNOWN)),
        Value::Transport(transport) => quote_transport(global, depth, transport, eq),
        Value::Prim(prim) => quote_prim(global, depth, prim),
        Value::Constant(constant) => quote_constant(global, depth, constant),
        Value::Rigid(rigid) => quote_rigid(global, depth, rigid),
        Value::Flex(flex) => quote_flex(global, depth, flex),
        _ => Err(Error::IllTyped),
    }
}

/// Quote an equality type to syntax.
pub fn quote_eq_type<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    eq: &val::EqType<'db>,
) -> Result<'db, RcSyntax<'db>> {
    let ty = type_quote(global, depth, &eq.ty)?;
    let lhs = quote(global, depth, &eq.lhs, &eq.ty)?;
    let rhs = quote(global, depth, &eq.rhs, &eq.ty)?;
    Ok(Syntax::eq_rc(Location::UNKNOWN, ty, lhs, rhs))
}

/// Quote a transport term to syntax.
fn quote_transport<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    transport: &val::Transport<'db>,
    eq: &val::EqType<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Quote the motive by eta-expansion
    // The motive is a closure with arity 1, so we create a single Closure wrapping the body
    let var = Rc::new(Value::variable(Level::new(depth), eq.ty.clone()));
    let motive_result = run_closure(global, &transport.motive, vec![var])?;
    let motive_body = type_quote(global, depth + 1, &motive_result)?;
    let motive = crate::syn::Closure::new(motive_body);

    // Quote the proof at the equality type
    let eq_ty = Rc::new(Value::eq(eq.ty.clone(), eq.lhs.clone(), eq.rhs.clone()));
    let proof = quote(global, depth, &transport.proof, &eq_ty)?;

    // Quote the value at the motive applied to lhs
    let lhs_ty = run_closure(global, &transport.motive, vec![eq.lhs.clone()])?;
    let value = quote(global, depth, &transport.value, &lhs_ty)?;

    Ok(Syntax::transport_rc(
        Location::UNKNOWN,
        motive,
        proof,
        value,
    ))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{Index, Level, UniverseLevel};
    use crate::eval;
    use crate::syn::parse::parse_syntax;
    use crate::syn::print::print_syntax_to_string;
    use crate::val::{DataConstructorInfo, TypeConstructorInfo};
    use crate::Database;
    use hwml_support::salsa::IntoWithDb;

    // =========================================================================
    // Test Context Helper
    // =========================================================================

    /// Test context with database and global environment for concise tests.
    struct Ctx<'db> {
        db: &'db Database,
        global: GlobalEnv<'db>,
    }

    impl<'db> Ctx<'db> {
        fn new(db: &'db Database) -> Self {
            Self {
                db,
                global: GlobalEnv::new(),
            }
        }

        /// Parse and evaluate a string to a value
        fn eval(&self, input: &'db str) -> Rc<Value<'db>> {
            let stx = parse_syntax(self.db, input).expect("parse failed");
            let mut env = Environment {
                global: &self.global,
                local: LocalEnv::new(),
                transparent: TransparentEnv::new(),
            };
            eval::eval(&mut env, &stx).expect("eval failed")
        }

        /// Parse, evaluate term and type, quote the term at the type, return string
        fn quote_at(&self, term: &'db str, ty: &'db str) -> String {
            let term_val = self.eval(term);
            let ty_val = self.eval(ty);
            let syntax = quote(&self.global, 0, &term_val, &ty_val).expect("quote failed");
            print_syntax_to_string(self.db, &syntax)
        }

        /// Parse, evaluate a type, and type-quote, returning a string
        fn quote_type(&self, term: &'db str) -> String {
            let val = self.eval(term);
            let syntax = type_quote(&self.global, 0, &val).expect("type_quote failed");
            print_syntax_to_string(self.db, &syntax)
        }

        /// Quote a value at a type and return the printed string
        fn q(&self, value: &Value<'db>, ty: &Value<'db>) -> String {
            let syntax = quote(&self.global, 0, value, ty).expect("quote failed");
            print_syntax_to_string(self.db, &syntax)
        }

        /// Quote a value at a type at a specific depth and return the printed string
        fn q_depth(&self, depth: usize, value: &Value<'db>, ty: &Value<'db>) -> String {
            let syntax = quote(&self.global, depth, value, ty).expect("quote failed");
            print_syntax_to_string(self.db, &syntax)
        }

        /// Quote a type and return the printed string
        fn tq(&self, ty: &Value<'db>) -> String {
            let syntax = type_quote(&self.global, 0, ty).expect("type_quote failed");
            print_syntax_to_string(self.db, &syntax)
        }

        /// Quote a type at a specific depth and return the printed string
        fn tq_depth(&self, depth: usize, ty: &Value<'db>) -> String {
            let syntax = type_quote(&self.global, depth, ty).expect("type_quote failed");
            print_syntax_to_string(self.db, &syntax)
        }

        // Common type constructors
        fn u0(&self) -> Rc<Value<'db>> {
            Rc::new(Value::universe(UniverseLevel::new(0)))
        }
        fn bit(&self) -> Rc<Value<'db>> {
            Rc::new(Value::bit())
        }

        /// Create Bit → Bit HArrow type
        fn harrow_bit_bit(&self) -> Value<'db> {
            Value::harrow(self.bit(), Closure::new(LocalEnv::new(), Syntax::bit_rc()))
        }

        /// Create ∀ (x : U0) → U0 Pi type
        fn pi_u0_u0(&self) -> Value<'db> {
            Value::pi(
                self.u0(),
                Closure::new(
                    LocalEnv::new(),
                    Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)),
                ),
            )
        }

        /// Create identity closure (returns variable at index 0)
        fn identity_closure(&self) -> Closure<'db> {
            Closure::new(
                LocalEnv::new(),
                Syntax::variable_rc(Location::UNKNOWN, Index(0)),
            )
        }
    }

    // =========================================================================
    // Type Universe Quotation Tests
    // =========================================================================

    #[test]
    fn test_quote_universes() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // Software universes
        assert_eq!(c.quote_type("U0"), "𝒰0");
        assert_eq!(c.quote_type("U1"), "𝒰1");
        // Hardware universes
        assert_eq!(c.quote_type("HardwareUniverse"), "HardwareUniverse");
        assert_eq!(c.quote_type("SignalUniverse"), "SignalUniverse");
        assert_eq!(c.quote_type("ModuleUniverse"), "ModuleUniverse");
    }

    // =========================================================================
    // Hardware Type Quotation Tests
    // =========================================================================

    #[test]
    fn test_quote_bit() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.quote_type("Bit"), "Bit");
    }

    #[test]
    fn test_quote_harrow() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.quote_type("Bit → Bit"), "Bit → Bit");
        // Chained: Bit → Bit → Bit
        assert_eq!(c.quote_type("Bit → Bit → Bit"), "Bit → Bit → Bit");
    }

    #[test]
    fn test_quote_slift() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.quote_type("^sBit"), "^sBit");
        // Nested: ^s^sBit
        assert_eq!(c.quote_type("^s^sBit"), "^s^sBit");
    }

    #[test]
    fn test_quote_mlift() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.quote_type("^m(Bit → Bit)"), "^m(Bit → Bit)");
        // Nested: ^m^m(Bit → Bit)
        assert_eq!(c.quote_type("^m^m(Bit → Bit)"), "^m^m(Bit → Bit)");
    }

    // =========================================================================
    // Value Quotation Tests (values at their types)
    // =========================================================================

    #[test]
    fn test_quote_bit_values() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.quote_at("0", "Bit"), "0");
        assert_eq!(c.quote_at("1", "Bit"), "1");
    }

    #[test]
    fn test_quote_type_at_universe() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // U0 is a value of type U1
        assert_eq!(c.quote_at("U0", "U1"), "𝒰0");
        // Bit is a value of type SignalUniverse
        assert_eq!(c.quote_at("Bit", "SignalUniverse"), "Bit");
        // HArrow is a value of type ModuleUniverse
        assert_eq!(c.quote_at("Bit → Bit", "ModuleUniverse"), "Bit → Bit");
    }

    // =========================================================================
    // Lambda/Module Quotation Tests
    // =========================================================================

    #[test]
    fn test_quote_modules() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // Identity: mod x → x
        assert_eq!(c.quote_at("mod %x → %x", "Bit → Bit"), "mod %0 → %0");
        // Constant: mod x → 0
        assert_eq!(c.quote_at("mod %x → 0", "Bit → Bit"), "mod %0 → 0");
    }

    #[test]
    fn test_quote_lambdas() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // Identity: λ x → x
        assert_eq!(c.quote_at("λ %x → %x", "∀ (%x : U0) → U0"), "λ %0 → %0");
    }

    // =========================================================================
    // Pi Type Quotation Tests
    // =========================================================================

    #[test]
    fn test_quote_pi_types() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // Simple: ∀ (x : U0) → U0
        assert_eq!(c.quote_type("∀ (%x : U0) → U0"), "∀ (%0 : 𝒰0) → 𝒰0");
        // Nested Pi collapses: ∀ (%0 : U0) (%1 : U0) → U0
        assert_eq!(
            c.quote_type("∀ (%x : U0) (%y : U0) → U0"),
            "∀ (%0 : 𝒰0) (%1 : 𝒰0) → 𝒰0"
        );
        // Dependent: ∀ (A : U0) → A
        assert_eq!(c.quote_type("∀ (%A : U0) → %A"), "∀ (%0 : 𝒰0) → %0");
    }

    // =========================================================================
    // Lift Type Quotation Tests
    // =========================================================================

    #[test]
    fn test_quote_lift() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // ^(^sBit)
        assert_eq!(c.quote_type("^^sBit"), "^^sBit");
        // ^(∀ (x : U0) → U0) - Pi inside Lift
        assert_eq!(c.quote_type("^∀ (%x : U0) → U0"), "^∀ (%0 : 𝒰0) → 𝒰0");
    }

    // =========================================================================
    // Neutral Term Quotation Tests (Rigid - variables)
    // =========================================================================

    #[test]
    fn test_quote_variables() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // Variable at level 1, quoted at depth 2 → Index(0) → prints as "!0" (unbound)
        let bit_var = Value::variable(Level::new(1), c.bit());
        assert_eq!(c.q_depth(2, &bit_var, &Value::bit()), "!0");
        // Same for universe-typed variable
        let u0_var = Value::variable(Level::new(1), c.u0());
        assert_eq!(
            c.q_depth(2, &u0_var, &Value::universe(UniverseLevel::new(0))),
            "!0"
        );
    }

    #[test]
    fn test_quote_constant_and_prim() {
        let db = Database::new();
        let c = Ctx::new(&db);
        let u0 = Value::universe(UniverseLevel::new(0));
        // Constant: @myConst
        let cid = "myConst".into_with_db(&db);
        assert_eq!(c.q(&Value::constant(cid), &u0), "@myConst");
        // Primitive: $Nat
        let pid = "Nat".into_with_db(&db);
        assert_eq!(c.q(&Value::prim(pid), &u0), "$Nat");
    }

    // =========================================================================
    // Eta-Expansion Tests
    // =========================================================================

    #[test]
    fn test_quote_eta_expansion() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // Pi types eta-expand neutrals: f : A → B becomes λx. f x
        let pi_ty = c.pi_u0_u0();
        let var = Value::variable(Level::new(0), Rc::new(pi_ty.clone()));
        // λ %0 → %0[%0] (function applied to its argument)
        assert_eq!(c.q(&var, &pi_ty), "λ %0 → %0[%0]");

        // HArrow types do NOT eta-expand neutrals
        let harrow_ty = c.harrow_bit_bit();
        let harrow_var = Value::variable(Level::new(1), Rc::new(harrow_ty.clone()));
        // Quote at depth 2: prints as !0 (no eta-expansion)
        assert_eq!(c.q_depth(2, &harrow_var, &harrow_ty), "!0");
    }

    // =========================================================================
    // Type Constructor Quotation Tests
    // =========================================================================

    #[test]
    fn test_quote_type_constructors() {
        let db = Database::new();
        let mut global = GlobalEnv::new();
        let u0 = Value::universe(UniverseLevel::new(0));

        // No args: #[@Nat]
        let nat_id = "Nat".into_with_db(&db);
        global.add_type_constructor(
            nat_id,
            TypeConstructorInfo::new(vec![], 0, UniverseLevel::new(0)),
        );
        let nat = Value::type_constructor(nat_id, vec![]);
        let syntax = quote(&global, 0, &nat, &u0).expect("quote");
        assert_eq!(print_syntax_to_string(&db, &syntax), "#[@Nat]");

        // With args: #[@Vec Bit]
        let vec_id = "Vec".into_with_db(&db);
        global.add_type_constructor(
            vec_id,
            TypeConstructorInfo::new(
                vec![Syntax::universe_rc(
                    Location::UNKNOWN,
                    UniverseLevel::new(0),
                )],
                1,
                UniverseLevel::new(0),
            ),
        );
        let vec_bit = Value::type_constructor(vec_id, vec![Rc::new(Value::bit())]);
        let syntax = quote(&global, 0, &vec_bit, &u0).expect("quote");
        assert_eq!(print_syntax_to_string(&db, &syntax), "#[@Vec Bit]");
    }

    // =========================================================================
    // Data Constructor Quotation Tests
    // =========================================================================

    #[test]
    fn test_quote_data_constructors() {
        let db = Database::new();
        let mut global = GlobalEnv::new();

        // Register Unit type and tt constructor
        let unit_id = "Unit".into_with_db(&db);
        global.add_type_constructor(
            unit_id,
            TypeConstructorInfo::new(vec![], 0, UniverseLevel::new(0)),
        );
        let tt_id = "tt".into_with_db(&db);
        global.add_data_constructor(
            tt_id,
            DataConstructorInfo::new(
                vec![],
                Syntax::type_constructor_rc(Location::UNKNOWN, unit_id, vec![]),
            ),
        );

        let unit_tcon = crate::val::TypeConstructor::new(unit_id, vec![]);
        let tt_dcon = Value::data_constructor(tt_id, vec![]);
        let syntax = quote_data_constructor(
            &global,
            0,
            match &tt_dcon {
                Value::DataConstructor(d) => d,
                _ => panic!(),
            },
            &unit_tcon,
        )
        .expect("quote");
        assert_eq!(print_syntax_to_string(&db, &syntax), "[@tt]");
    }

    // =========================================================================
    // Metavariable Quotation Tests
    // =========================================================================

    #[test]
    fn test_quote_metavariables() {
        use crate::common::MetaVariableId;
        let db = Database::new();
        let mut global = GlobalEnv::new();
        let u0 = Value::universe(UniverseLevel::new(0));
        let u0_rc = Rc::new(u0.clone());

        // No args: ?[0]
        let meta_id = MetaVariableId::new(Location::UNKNOWN, 0);
        global.add_metavariable(
            meta_id,
            vec![],
            Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)),
        );
        let meta = Value::metavariable(meta_id, LocalEnv::new(), u0_rc.clone());
        let syntax = quote(&global, 0, &meta, &u0).expect("quote");
        assert_eq!(print_syntax_to_string(&db, &syntax), "?[0]");

        // With args: ?[1 Bit]
        let meta_id2 = MetaVariableId::new(Location::UNKNOWN, 1);
        global.add_metavariable(
            meta_id2,
            vec![Syntax::universe_rc(
                Location::UNKNOWN,
                UniverseLevel::new(0),
            )],
            Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)),
        );
        let mut local = LocalEnv::new();
        local.push(Rc::new(Value::bit()));
        let meta2 = Value::metavariable(meta_id2, local, u0_rc);
        let syntax = quote(&global, 0, &meta2, &u0).expect("quote");
        assert_eq!(print_syntax_to_string(&db, &syntax), "?[1 Bit]");
    }

    // =========================================================================
    // Mixed Depth and Complex Tests
    // =========================================================================

    #[test]
    fn test_quote_nested_binder_depths() {
        let db = Database::new();
        let c = Ctx::new(&db);

        // ∀ (A : U0) → ∀ (x : A) → A
        let inner = Syntax::pi_rc(
            Location::UNKNOWN,
            Syntax::variable_rc(Location::UNKNOWN, Index(0)), // domain is A
            Syntax::variable_rc(Location::UNKNOWN, Index(1)), // codomain is A
        );
        let outer = Value::pi(c.u0(), Closure::new(LocalEnv::new(), inner));
        assert_eq!(c.tq(&outer), "∀ (%0 : 𝒰0) (%1 : %0) → %0");
    }

    #[test]
    fn test_quote_lift_with_neutral() {
        let db = Database::new();
        let c = Ctx::new(&db);

        // ^s(x) where x is a variable
        let var = Value::variable(Level::new(0), Rc::new(Value::signal_universe()));
        let slift = Value::slift(Rc::new(var));
        assert_eq!(c.tq_depth(1, &slift), "^s!0");
    }

    // =========================================================================
    // HApplication Quotation Tests
    // =========================================================================

    #[test]
    fn test_quote_happlication() {
        let db = Database::new();
        let c = Ctx::new(&db);

        // Create id<Bit>(0) - identity module applied to 0
        // First, the module type: Bit → Bit
        let harrow_ty = c.harrow_bit_bit();
        // The identity module: mod x → x
        let id_mod = Value::module(c.identity_closure());
        // Apply it to zero: id<Bit>(0)
        let happ = Value::happlication(
            Rc::new(id_mod),
            Rc::new(harrow_ty.clone()),
            Rc::new(Value::zero()),
        );
        // The result type is Bit (codomain of harrow applied to zero)
        // Note: printer doesn't parenthesize the module
        assert_eq!(c.q(&happ, &Value::bit()), "mod %0 → %0<Bit>(0)");
    }

    // =========================================================================
    // String-Based Neutral Quotation Tests (using lambda pattern)
    // =========================================================================

    #[test]
    fn test_quote_neutral_via_lambda() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // λ f → f ^Bit - the body (f ^Bit) is a neutral application
        // Note: A → B parses as HArrow, not Pi. Use ∀ (%x : A) → B for Pi.
        assert_eq!(
            c.quote_at("λ %f → %f ^Bit", "∀ (%f : ∀ (%x : U0) → U0) → U0"),
            "λ %0 → %0[^Bit]"
        );
    }

    #[test]
    fn test_quote_neutral_variable_in_lambda() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // λ x → x at type ∀ (x : Bit) → Bit gives λ %0 → %0
        assert_eq!(c.quote_at("λ %x → %x", "∀ (%x : Bit) → Bit"), "λ %0 → %0");
    }

    #[test]
    fn test_quote_neutral_nested_application() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // λ f → λ g → f (g ^Bit) - nested neutral applications
        // f : ∀ (x : U0) → U0, g : ∀ (x : U0) → U0
        // Note: printer collapses nested lambdas into multi-binder form
        assert_eq!(
            c.quote_at(
                "λ %f → λ %g → %f (%g ^Bit)",
                "∀ (%f : ∀ (%x : U0) → U0) (%g : ∀ (%x : U0) → U0) → U0"
            ),
            "λ %0 %1 → %0[%1[^Bit]]"
        );
    }

    #[test]
    fn test_quote_module_neutral() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // mod x → x at type Bit → Bit
        assert_eq!(c.quote_at("mod %x → %x", "Bit → Bit"), "mod %0 → %0");
        // mod x → 0 (constant module)
        assert_eq!(c.quote_at("mod %x → 0", "Bit → Bit"), "mod %0 → 0");
    }

    // =========================================================================
    // Equality Type Quotation Tests
    // =========================================================================

    #[test]
    fn test_quote_eq_type() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // Eq Bit 0 1
        assert_eq!(c.quote_type("Eq Bit 0 1"), "Eq Bit 0 1");
    }

    #[test]
    fn test_quote_refl() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // refl at Eq Bit 0 0
        assert_eq!(c.quote_at("refl", "Eq Bit 0 0"), "refl");
    }

    #[test]
    fn test_quote_transport() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // transport [%0] |- Bit refl 0 reduces to 0 during eval
        // So we just verify the reduction works
        assert_eq!(c.quote_at("transport [%0] |- Bit refl 0", "Bit"), "0");
    }

    #[test]
    fn test_quote_nested_eq() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // Eq (Eq U0 U0 U0) refl refl
        assert_eq!(
            c.quote_type("Eq (Eq U0 U0 U0) refl refl"),
            "Eq (Eq 𝒰0 𝒰0 𝒰0) refl refl"
        );
    }
}
