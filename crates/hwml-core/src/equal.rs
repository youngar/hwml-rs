use crate::{
    common::{Level, MetaVariableId},
    eval::{self, run_closure},
    val::{
        self, Application, Case, DataConstructor, Eliminator, Environment, Flex, GlobalEnv, HArrow,
        LocalEnv, Module, Normal, Pi, Rigid, Spine, TypeConstructor,
    },
    ConstantId, UniverseLevel, Value,
};
use itertools::izip;
use std::rc::Rc;

#[derive(Debug, Clone)]
#[deny(elided_lifetimes_in_paths)]
pub enum Error<'db> {
    /// Indicates that the terms are not convertible.
    NotConvertible,
    /// Indicates that the terms are not well-typed, so convertibility cannot be checked.
    IllTyped,
    EvalError(eval::Error),
    LookupError(val::LookupError<'db>),
}

impl<'db> From<eval::Error> for Error<'db> {
    fn from(err: eval::Error) -> Self {
        Error::EvalError(err)
    }
}

type Result<'db> = std::result::Result<(), Error<'db>>;

pub fn equate<'a, 'db: 'a>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    ty: &Value<'db>,
) -> Result<'db> {
    match ty {
        Value::Universe(universe) => equate_universe_instances(global, depth, lhs, rhs, universe),
        Value::Lift(lift) => equate_lift_instances(global, depth, lhs, rhs, lift),
        Value::Pi(pi) => equate_pi_instances(global, depth, lhs, rhs, pi),
        Value::TypeConstructor(tcon) => {
            equate_type_constructor_instances(global, depth, lhs, rhs, tcon)
        }
        Value::HardwareUniverse(hwuniverse) => {
            equate_hwuniverse_instances(global, depth, lhs, rhs, hwuniverse)
        }
        Value::SignalUniverse(signal_universe) => {
            equate_signal_universe_instances(global, depth, lhs, rhs, signal_universe)
        }
        Value::ModuleUniverse(module_universe) => {
            equate_module_universe_instances(global, depth, lhs, rhs, module_universe)
        }
        Value::Prim(prim) => equate_prim_instances(global, depth, lhs, rhs, prim),
        Value::Constant(constant) => equate_constant_instances(global, depth, lhs, rhs, constant),
        Value::Rigid(rigid) => equate_rigid_instances(global, depth, lhs, rhs, rigid),
        Value::Flex(flex) => equate_flex_instances(global, depth, lhs, rhs, flex),
        Value::EqType(eq) => equate_eq_instances(global, depth, lhs, rhs, eq),
        _ => Err(Error::IllTyped),
    }
}

pub fn equate_universe_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    _universe: &val::Universe<'db>,
) -> Result<'db> {
    type_equiv(global, depth, lhs, rhs)
}

pub fn equate_lift_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    lift: &val::Lift<'db>,
) -> Result<'db> {
    match lift.ty.as_ref() {
        Value::SLift(slift) => equate_slift_instances(global, depth, lhs, rhs, slift),
        Value::MLift(mlift) => equate_mlift_instances(global, depth, lhs, rhs, mlift),
        // ^Bit evaluates to Lift(Bit) directly, not Lift(SLift(Bit))
        Value::Bit(bit) => equate_bit_instances(global, depth, lhs, rhs, bit),
        _ => Err(Error::IllTyped),
    }
}

pub fn equate_pi_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    pi: &Pi<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        (Value::Lambda(lhs), Value::Lambda(rhs)) => equate_lambdas(global, depth, lhs, rhs, pi),
        (Value::Prim(lhs), Value::Prim(rhs)) => equate_prims(global, depth, lhs, rhs),
        (Value::Constant(lhs), Value::Constant(rhs)) => equate_constants(global, depth, lhs, rhs),
        (Value::Rigid(lhs), Value::Rigid(rhs)) => equate_rigids(global, depth, lhs, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => equate_flexes(global, depth, lhs, rhs),
        _ => Err(Error::NotConvertible),
    }
}

pub fn equate_type_constructor_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    tcon: &TypeConstructor<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        (Value::DataConstructor(lhs), Value::DataConstructor(rhs)) => {
            equate_data_constructors(global, depth, lhs, rhs, tcon)
        }
        (Value::Prim(lhs), Value::Prim(rhs)) => equate_prims(global, depth, lhs, rhs),
        (Value::Constant(lhs), Value::Constant(rhs)) => equate_constants(global, depth, lhs, rhs),
        (Value::Rigid(lhs), Value::Rigid(rhs)) => equate_rigids(global, depth, lhs, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => equate_flexes(global, depth, lhs, rhs),
        _ => Err(Error::NotConvertible),
    }
}

pub fn equate_hwuniverse_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    _hwuniverse: &val::HardwareUniverse<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        (Value::SLift(lhs), Value::SLift(rhs)) => equate_slifts(global, depth, lhs, rhs),
        (Value::MLift(lhs), Value::MLift(rhs)) => equate_mlifts(global, depth, lhs, rhs),
        (Value::Prim(lhs), Value::Prim(rhs)) => equate_prims(global, depth, lhs, rhs),
        (Value::Constant(lhs), Value::Constant(rhs)) => equate_constants(global, depth, lhs, rhs),
        (Value::Rigid(lhs), Value::Rigid(rhs)) => equate_rigids(global, depth, lhs, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => equate_flexes(global, depth, lhs, rhs),
        _ => Err(Error::NotConvertible),
    }
}

pub fn equate_slift_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    slift: &val::SLift<'db>,
) -> Result<'db> {
    match slift.ty.as_ref() {
        Value::Bit(bit) => equate_bit_instances(global, depth, lhs, rhs, bit),
        _ => Err(Error::IllTyped),
    }
}

pub fn equate_mlift_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    mlift: &val::MLift<'db>,
) -> Result<'db> {
    match mlift.ty.as_ref() {
        Value::HArrow(harrow) => equate_harrows_instances(global, depth, lhs, rhs, harrow),
        _ => Err(Error::IllTyped),
    }
}

pub fn equate_harrows_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    harrow: &HArrow<'db>,
) -> Result<'db> {
    // HArrow instances do not eta-expand like Arrow instances.
    // Module is the canonical instance of HArrow.
    match (lhs, rhs) {
        (Value::Module(lhs), Value::Module(rhs)) => equate_modules(global, depth, lhs, rhs, harrow),
        (Value::Prim(lhs), Value::Prim(rhs)) => equate_prims(global, depth, lhs, rhs),
        (Value::Constant(lhs), Value::Constant(rhs)) => equate_constants(global, depth, lhs, rhs),
        (Value::Rigid(lhs), Value::Rigid(rhs)) => equate_rigids(global, depth, lhs, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => equate_flexes(global, depth, lhs, rhs),
        _ => Err(Error::NotConvertible),
    }
}

pub fn equate_bit_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    _bit: &val::Bit<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        (Value::Zero(_), Value::Zero(_)) => Ok(()),
        (Value::One(_), Value::One(_)) => Ok(()),
        (Value::Prim(lhs), Value::Prim(rhs)) => equate_prims(global, depth, lhs, rhs),
        (Value::Constant(lhs), Value::Constant(rhs)) => equate_constants(global, depth, lhs, rhs),
        (Value::Rigid(lhs), Value::Rigid(rhs)) => equate_rigids(global, depth, lhs, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => equate_flexes(global, depth, lhs, rhs),
        _ => Err(Error::NotConvertible),
    }
}

pub fn equate_signal_universe_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    _signal_universe: &val::SignalUniverse<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        (Value::Bit(lhs), Value::Bit(rhs)) => equate_bits(global, depth, lhs, rhs),
        (Value::Prim(lhs), Value::Prim(rhs)) => equate_prims(global, depth, lhs, rhs),
        (Value::Constant(lhs), Value::Constant(rhs)) => equate_constants(global, depth, lhs, rhs),
        (Value::Rigid(lhs), Value::Rigid(rhs)) => equate_rigids(global, depth, lhs, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => equate_flexes(global, depth, lhs, rhs),
        _ => Err(Error::NotConvertible),
    }
}

pub fn equate_module_universe_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    _module_universe: &val::ModuleUniverse<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        (Value::HArrow(lhs), Value::HArrow(rhs)) => equate_harrows(global, depth, lhs, rhs),
        (Value::Prim(lhs), Value::Prim(rhs)) => equate_prims(global, depth, lhs, rhs),
        (Value::Constant(lhs), Value::Constant(rhs)) => equate_constants(global, depth, lhs, rhs),
        (Value::Rigid(lhs), Value::Rigid(rhs)) => equate_rigids(global, depth, lhs, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => equate_flexes(global, depth, lhs, rhs),
        _ => Err(Error::NotConvertible),
    }
}

pub fn equate_constant_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    _constant: &ConstantId<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        (Value::Prim(lhs), Value::Prim(rhs)) => equate_prims(global, depth, lhs, rhs),
        (Value::Constant(lhs), Value::Constant(rhs)) => equate_constants(global, depth, lhs, rhs),
        (Value::Rigid(lhs), Value::Rigid(rhs)) => equate_rigids(global, depth, lhs, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => equate_flexes(global, depth, lhs, rhs),
        _ => Err(Error::NotConvertible),
    }
}

pub fn equate_prim_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    _prim: &ConstantId<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        (Value::Prim(lhs), Value::Prim(rhs)) => equate_prims(global, depth, lhs, rhs),
        (Value::Constant(lhs), Value::Constant(rhs)) => equate_constants(global, depth, lhs, rhs),
        (Value::Rigid(lhs), Value::Rigid(rhs)) => equate_rigids(global, depth, lhs, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => equate_flexes(global, depth, lhs, rhs),
        _ => Err(Error::NotConvertible),
    }
}

pub fn equate_rigid_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    _rigid: &Rigid<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        (Value::Prim(lhs), Value::Prim(rhs)) => equate_prims(global, depth, lhs, rhs),
        (Value::Constant(lhs), Value::Constant(rhs)) => equate_constants(global, depth, lhs, rhs),
        (Value::Rigid(lhs), Value::Rigid(rhs)) => equate_rigids(global, depth, lhs, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => equate_flexes(global, depth, lhs, rhs),
        _ => Err(Error::NotConvertible),
    }
}

pub fn equate_flex_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    _flex: &Flex<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        (Value::Prim(lhs), Value::Prim(rhs)) => equate_prims(global, depth, lhs, rhs),
        (Value::Constant(lhs), Value::Constant(rhs)) => equate_constants(global, depth, lhs, rhs),
        (Value::Rigid(lhs), Value::Rigid(rhs)) => equate_rigids(global, depth, lhs, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => equate_flexes(global, depth, lhs, rhs),
        _ => Err(Error::NotConvertible),
    }
}

pub fn type_equiv<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        (Value::Pi(lhs), Value::Pi(rhs)) => equate_pis(global, depth, lhs, rhs),
        (Value::TypeConstructor(lhs), Value::TypeConstructor(rhs)) => {
            equate_type_constructors(global, depth, lhs, rhs)
        }
        (Value::Universe(lhs), Value::Universe(rhs)) => equate_universes(global, depth, lhs, rhs),
        (Value::Rigid(lhs), Value::Rigid(rhs)) => equate_rigids(global, depth, lhs, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => equate_flexes(global, depth, lhs, rhs),
        (Value::Prim(lhs), Value::Prim(rhs)) => equate_prims(global, depth, lhs, rhs),
        (Value::Constant(lhs), Value::Constant(rhs)) => equate_constants(global, depth, lhs, rhs),

        // HardwareUniverse types that can appear as meta-level types
        (Value::Lift(lhs), Value::Lift(rhs)) => equate_lifts(global, depth, lhs, rhs),

        // SLift and MLift are hardware type constructors
        (Value::SLift(lhs), Value::SLift(rhs)) => slift_equiv(global, depth, lhs, rhs),
        (Value::MLift(lhs), Value::MLift(rhs)) => mlift_equiv(global, depth, lhs, rhs),

        // Bit is a hardware type (equivalent types if both are Bit)
        (Value::Bit(_), Value::Bit(_)) => Ok(()),

        // Equality types
        (Value::EqType(lhs), Value::EqType(rhs)) => equate_eq_types(global, depth, lhs, rhs),

        _ => Err(Error::NotConvertible),
    }
}

/// Compare two SLift types.
/// SLift types contain signal types (like Bit).
pub fn slift_equiv<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &val::SLift<'db>,
    rhs: &val::SLift<'db>,
) -> Result<'db> {
    signal_type_equiv(global, depth, &lhs.ty, &rhs.ty)
}

/// Compare two MLift types.
/// MLift types contain module types (like HArrow).
pub fn mlift_equiv<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &val::MLift<'db>,
    rhs: &val::MLift<'db>,
) -> Result<'db> {
    module_type_equiv(global, depth, &lhs.ty, &rhs.ty)
}

/// Compare two signal types (types in SignalUniverse).
/// Handles Bit and the 4 variable-like constructs.
pub fn signal_type_equiv<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        (Value::Bit(_), Value::Bit(_)) => Ok(()),
        (Value::Prim(lhs), Value::Prim(rhs)) => equate_prims(global, depth, lhs, rhs),
        (Value::Constant(lhs), Value::Constant(rhs)) => equate_constants(global, depth, lhs, rhs),
        (Value::Rigid(lhs), Value::Rigid(rhs)) => equate_rigids(global, depth, lhs, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => equate_flexes(global, depth, lhs, rhs),
        _ => Err(Error::NotConvertible),
    }
}

/// Compare two module types (types in ModuleUniverse).
/// Handles HArrow and the 4 variable-like constructs.
pub fn module_type_equiv<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        (Value::HArrow(lhs), Value::HArrow(rhs)) => equate_harrows(global, depth, lhs, rhs),
        (Value::Prim(lhs), Value::Prim(rhs)) => equate_prims(global, depth, lhs, rhs),
        (Value::Constant(lhs), Value::Constant(rhs)) => equate_constants(global, depth, lhs, rhs),
        (Value::Rigid(lhs), Value::Rigid(rhs)) => equate_rigids(global, depth, lhs, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => equate_flexes(global, depth, lhs, rhs),
        _ => Err(Error::NotConvertible),
    }
}

pub fn equate_universes<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &val::Universe<'db>,
    rhs: &val::Universe<'db>,
) -> Result<'db> {
    let lhs = lhs.level;
    let rhs = rhs.level;
    equate_universe_levels(global, depth, lhs, rhs)
}

pub fn equate_lifts<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &val::Lift<'db>,
    rhs: &val::Lift<'db>,
) -> Result<'db> {
    let lhs_ty = &lhs.ty;
    let rhs_ty = &rhs.ty;
    type_equiv(global, depth, lhs_ty, rhs_ty)
}

pub fn equate_pis<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Pi<'db>,
    rhs: &Pi<'db>,
) -> Result<'db> {
    type_equiv(global, depth, &lhs.source, &rhs.source)?;
    let arg = Rc::new(Value::variable(Level::new(depth), lhs.source.clone()));
    let self_target = run_closure(global, &lhs.target, [arg.clone()])?;
    let other_target = run_closure(global, &rhs.target, [arg])?;
    type_equiv(global, depth + 1, &self_target, &other_target)
}

/// Compare two lambdas at a given Pi type.
/// Lambdas are the canonical instances of Pi types.
pub fn equate_lambdas<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &val::Lambda<'db>,
    rhs: &val::Lambda<'db>,
    pi: &Pi<'db>,
) -> Result<'db> {
    // Create a fresh variable of the source type
    let arg = Rc::new(Value::variable(Level::new(depth), pi.source.clone()));

    // Apply both lambda bodies to the fresh variable
    let lhs_result = run_closure(global, &lhs.body, [arg.clone()])?;
    let rhs_result = run_closure(global, &rhs.body, [arg.clone()])?;

    // Get the result type by running the Pi's target closure
    let result_ty = run_closure(global, &pi.target, [arg])?;

    // Compare the results at the result type
    equate(global, depth + 1, &lhs_result, &rhs_result, &result_ty)
}

fn equate_type_constructors<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &TypeConstructor<'db>,
    rhs: &TypeConstructor<'db>,
) -> Result<'db> {
    // Check that the constructor is the same.
    let constructor = lhs.constructor;
    if constructor != rhs.constructor {
        return Err(Error::NotConvertible);
    }

    // Look up the type info.
    let type_info = global
        .type_constructor(constructor)
        .map_err(Error::LookupError)?
        .clone();

    // Create a new environment.
    let mut env = Environment {
        global: &global,
        local: LocalEnv::new(),
    };

    // Compare each argument.
    for (larg, rarg, syn_ty) in izip!(lhs.iter(), rhs.iter(), type_info.arguments.iter()) {
        // Evaluate the type of the current argument.
        let sem_ty = eval::eval(&mut env, &syn_ty)?;

        // Check that the arguments are convertible at the evaluated type.
        equate(global, depth, &larg, &rarg, &sem_ty)?;

        // Push the semantic argument into the environment for subsequent iterations.
        env.push(larg.clone());
    }
    Ok(())
}

fn equate_data_constructors<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &DataConstructor<'db>,
    rhs: &DataConstructor<'db>,
    ty: &TypeConstructor<'db>,
) -> Result<'db> {
    // Get the constructor constant.
    let constructor = lhs.constructor;
    if constructor != rhs.constructor {
        return Err(Error::NotConvertible);
    }

    // Look up the type constructor info.
    let type_info = global
        .type_constructor(ty.constructor)
        .map_err(Error::LookupError)?
        .clone();

    // Look up the data constructor info.
    let data_info = global
        .data_constructor(constructor)
        .map_err(Error::LookupError)?
        .clone();

    // Find the number of parameters.
    let num_parameters = type_info.num_parameters();

    // Create an array of just the parameters, leaving out indices.
    let parameters = ty.iter().take(num_parameters).cloned();

    // Create an environment for evaluating the type of each argument, with
    // parameters in the context.
    let mut env = Environment {
        global: global,
        local: LocalEnv::new(),
    };
    env.extend(parameters);

    // TODO: We are not adding the parameters to the binding depth, which is used
    // to check if two terms are convertible. The environment only extends for the
    // types.
    // depth = depth + num_parameters;

    for (larg, rarg, syn_ty) in izip!(lhs.iter(), rhs.iter(), data_info.arguments.iter()) {
        // Evaluate the type of the current argument.
        let sem_ty = eval::eval(&mut env, &syn_ty).map_err(Error::EvalError)?;

        // Check that the arguments are convertible at the evaluated type.
        equate(global, depth, &larg, &rarg, &sem_ty)?;

        // Push the semantic argument into the environment for subsequent iterations.
        env.push(larg.clone());
    }
    Ok(())
}

pub fn equate_hardware_universes<'db>(
    _global: &GlobalEnv<'db>,
    _depth: usize,
    _lhs: &val::HardwareUniverse<'db>,
    _rhs: &val::HardwareUniverse<'db>,
) -> Result<'db> {
    Ok(())
}

pub fn equate_slifts<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &val::SLift<'db>,
    rhs: &val::SLift<'db>,
) -> Result<'db> {
    type_equiv(global, depth, &lhs.ty, &rhs.ty)
}

pub fn equate_mlifts<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &val::MLift<'db>,
    rhs: &val::MLift<'db>,
) -> Result<'db> {
    type_equiv(global, depth, &lhs.ty, &rhs.ty)
}

pub fn equate_prims<'db>(
    _global: &GlobalEnv<'db>,
    _depth: usize,
    lhs: &ConstantId<'db>,
    rhs: &ConstantId<'db>,
) -> Result<'db> {
    // For now, just compare by identity. Eventually we may look up info in
    // GlobalEnv.
    if lhs == rhs {
        Ok(())
    } else {
        Err(Error::NotConvertible)
    }
}

pub fn equate_constants<'db>(
    _global: &GlobalEnv<'db>,
    _depth: usize,
    lhs: &ConstantId<'db>,
    rhs: &ConstantId<'db>,
) -> Result<'db> {
    // For now, just compare by identity. Eventually we may look up and unfold
    // definitions.
    if lhs == rhs {
        Ok(())
    } else {
        Err(Error::NotConvertible)
    }
}

pub fn equate_rigids<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Rigid<'db>,
    rhs: &Rigid<'db>,
) -> Result<'db> {
    // Check that the heads are the same variable.
    equate_levels(global, depth, lhs.head.level, rhs.head.level)?;
    // Check that the spines are convertible.
    equate_spines(global, depth, &lhs.spine, &rhs.spine)
}

pub fn equate_flexes<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Flex<'db>,
    rhs: &Flex<'db>,
) -> Result<'db> {
    // Check that the heads are the same metavariable.
    equate_metavariable_ids(global, depth, lhs.head.id, rhs.head.id)?;
    // Check that the spines are convertible.
    equate_spines(global, depth, &lhs.spine, &rhs.spine)
}

pub fn equate_bits<'db>(
    _global: &GlobalEnv<'db>,
    _depth: usize,
    _lhs: &val::Bit<'db>,
    _rhs: &val::Bit<'db>,
) -> Result<'db> {
    // All Bit types are equal
    Ok(())
}

pub fn equate_harrows<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &HArrow<'db>,
    rhs: &HArrow<'db>,
) -> Result<'db> {
    // Check that source hardware types are convertible
    type_equiv(global, depth, &lhs.source, &rhs.source)?;
    // For target, we need to apply to a fresh variable and compare
    let arg = Rc::new(Value::variable(Level::new(depth), lhs.source.clone()));
    let lhs_target = run_closure(global, &lhs.target, [arg.clone()])?;
    let rhs_target = run_closure(global, &rhs.target, [arg])?;
    type_equiv(global, depth + 1, &lhs_target, &rhs_target)
}

/// Compare two modules at a given HArrow type.
/// Modules are the instances of HArrow types (hardware function types).
pub fn equate_modules<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Module<'db>,
    rhs: &Module<'db>,
    harrow: &HArrow<'db>,
) -> Result<'db> {
    // Create a fresh variable of the source type
    let arg = Rc::new(Value::variable(Level::new(depth), harrow.source.clone()));

    // Apply both module bodies to the fresh variable
    let lhs_result = run_closure(global, &lhs.body, [arg.clone()])?;
    let rhs_result = run_closure(global, &rhs.body, [arg.clone()])?;

    // Get the result type by running the HArrow's target closure
    let result_ty = run_closure(global, &harrow.target, [arg])?;

    // Compare the results at the result type
    equate(global, depth + 1, &lhs_result, &rhs_result, &result_ty)
}

pub fn equate_spines<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Spine<'db>,
    rhs: &Spine<'db>,
) -> Result<'db> {
    // Check that the spines have the same length.
    if lhs.len() != rhs.len() {
        return Err(Error::NotConvertible);
    }

    // Check that each eliminator is convertible.
    for (l, r) in lhs.iter().zip(rhs.iter()) {
        equate_eliminators(global, depth, l, r)?;
    }

    Ok(())
}

pub fn equate_eliminators<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Eliminator<'db>,
    rhs: &Eliminator<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        (Eliminator::Application(lhs), Eliminator::Application(rhs)) => {
            equate_applications(global, depth, lhs, rhs)
        }
        (Eliminator::Case(lhs), Eliminator::Case(rhs)) => equate_cases(global, depth, lhs, rhs),
        _ => Err(Error::NotConvertible),
    }
}

pub fn equate_applications<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Application<'db>,
    rhs: &Application<'db>,
) -> Result<'db> {
    // Compare arguments - but we need the type to do proper typed equality
    // For now, do structural comparison
    equate_normals(global, depth, &lhs.argument, &rhs.argument)
}

pub fn equate_normals<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Normal<'db>,
    rhs: &Normal<'db>,
) -> Result<'db> {
    // First check that types are equal
    type_equiv(global, depth, &lhs.ty, &rhs.ty)?;
    // Then check values at that type
    equate(global, depth, &lhs.value, &rhs.value, &lhs.ty)
}

/// Check that two case eliminators are convertible.
///
/// With the simple (non-dependent) return type design, we compare return types
/// directly rather than comparing motives.
pub fn equate_cases<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Case<'db>,
    rhs: &Case<'db>,
) -> Result<'db> {
    // Check that the type constructors are the same.
    if lhs.type_constructor != rhs.type_constructor {
        return Err(Error::NotConvertible);
    }

    // Look up the type constructor info.
    let type_info = global
        .type_constructor(lhs.type_constructor)
        .map_err(Error::LookupError)?
        .clone();

    // Check that the parameters are convertible.
    // Create an environment for evaluating the type of each parameter.
    let mut env = Environment {
        global: global,
        local: LocalEnv::new(),
    };

    for (lparam, rparam, syn_ty) in izip!(
        lhs.parameters.iter(),
        rhs.parameters.iter(),
        type_info.parameters().iter()
    ) {
        // Evaluate the type of the current parameter.
        let sem_ty = eval::eval(&mut env, syn_ty).map_err(Error::EvalError)?;

        // Check that the parameters are convertible at the evaluated type.
        equate(global, depth, &lparam, &rparam, &sem_ty)?;

        // Push the semantic parameter into the environment for subsequent iterations.
        env.push(lparam.clone());
    }

    // No return_type comparison needed - case expressions are check-only,
    // so the return type comes from the expected type context.

    // Check that the branches are convertible.
    // First, check that we have the same number of branches.
    if lhs.branches.len() != rhs.branches.len() {
        return Err(Error::NotConvertible);
    }

    // For checking branch bodies, we need a type. Without return_type, we use a placeholder.
    // TODO: Thread the expected type through when we have check-only equate.
    let placeholder_ty = Rc::new(Value::Universe(val::Universe::new(UniverseLevel::new(0))));

    // Check each branch.
    for (lbranch, rbranch) in izip!(lhs.branches.iter(), rhs.branches.iter()) {
        // Check that the constructors are the same.
        if lbranch.constructor != rbranch.constructor {
            return Err(Error::NotConvertible);
        }

        // Check that the arities are the same.
        if lbranch.arity != rbranch.arity {
            return Err(Error::NotConvertible);
        }

        // Look up the data constructor info.
        let data_info = global
            .data_constructor(lbranch.constructor)
            .map_err(Error::LookupError)?
            .clone();

        // Create fresh variables for the data constructor arguments.
        let dcon_arg_tys =
            eval::eval_telescope(global, lhs.parameters.clone(), &data_info.arguments)?;
        let mut dcon_args = Vec::new();
        for ty in dcon_arg_tys.types {
            dcon_args.push(Rc::new(Value::variable(
                Level::new(depth + dcon_args.len()),
                ty,
            )));
        }

        // Apply both branch bodies to the same data constructor arguments.
        let lbranch_val = run_closure(global, &lbranch.body, dcon_args.clone())?;
        let rbranch_val = run_closure(global, &rbranch.body, dcon_args)?;

        // Check that the branch values are convertible.
        // TODO: Use the actual expected type from check context instead of placeholder.
        equate(
            global,
            depth + lbranch.arity,
            &lbranch_val,
            &rbranch_val,
            &placeholder_ty,
        )?;
    }

    Ok(())
}

// ============================================================================
// Equality Type Support
// ============================================================================

/// Check that two instances of an equality type are convertible.
/// At type `Eq A x y`, the instances must be proofs of equality.
pub fn equate_eq_instances<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
    eq: &val::EqType<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        // Two refl proofs are always equal
        (Value::Refl(_), Value::Refl(_)) => Ok(()),
        // Transport terms: compare structurally
        (Value::Transport(lhs_t), Value::Transport(rhs_t)) => {
            equate_transports(global, depth, lhs_t, rhs_t, eq)
        }
        // Neutral proofs: compare as neutrals
        (Value::Prim(lhs), Value::Prim(rhs)) => equate_prims(global, depth, lhs, rhs),
        (Value::Constant(lhs), Value::Constant(rhs)) => equate_constants(global, depth, lhs, rhs),
        (Value::Rigid(lhs), Value::Rigid(rhs)) => equate_rigids(global, depth, lhs, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => equate_flexes(global, depth, lhs, rhs),
        _ => Err(Error::NotConvertible),
    }
}

/// Check that two equality types are convertible.
/// Eq A x y ≡ Eq B u v  iff  A ≡ B, x ≡ u, and y ≡ v
fn equate_eq_types<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &val::EqType<'db>,
    rhs: &val::EqType<'db>,
) -> Result<'db> {
    // Check that the types are equivalent
    type_equiv(global, depth, &lhs.ty, &rhs.ty)?;
    // Check that the left-hand sides are equal at that type
    equate(global, depth, &lhs.lhs, &rhs.lhs, &lhs.ty)?;
    // Check that the right-hand sides are equal at that type
    equate(global, depth, &lhs.rhs, &rhs.rhs, &lhs.ty)?;
    Ok(())
}

/// Check that two transport terms are convertible.
fn equate_transports<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &val::Transport<'db>,
    rhs: &val::Transport<'db>,
    eq: &val::EqType<'db>,
) -> Result<'db> {
    // Compare proofs at the equality type
    let eq_ty = Rc::new(Value::eq(eq.ty.clone(), eq.lhs.clone(), eq.rhs.clone()));
    equate(global, depth, &lhs.proof, &rhs.proof, &eq_ty)?;

    // Compare values at the motive applied to lhs
    // P x where P is the motive
    let lhs_ty = run_closure(global, &lhs.motive, vec![eq.lhs.clone()])?;
    equate(global, depth, &lhs.value, &rhs.value, &lhs_ty)?;

    // Compare motives by eta-expansion
    // Create a fresh variable and compare P x for both motives
    let var = Rc::new(Value::variable(Level::new(depth), eq.ty.clone()));
    let lhs_result = run_closure(global, &lhs.motive, vec![var.clone()])?;
    let rhs_result = run_closure(global, &rhs.motive, vec![var])?;

    // The result type is a universe (motives are type families)
    // We use type_equiv to compare the results
    type_equiv(global, depth + 1, &lhs_result, &rhs_result)?;

    Ok(())
}

pub fn equate_universe_levels<'db>(
    _global: &GlobalEnv<'db>,
    _depth: usize,
    lhs: UniverseLevel,
    rhs: UniverseLevel,
) -> Result<'db> {
    if lhs == rhs {
        Ok(())
    } else {
        Err(Error::NotConvertible)
    }
}

pub fn equate_constant_ids<'db>(
    _global: &GlobalEnv<'db>,
    _depth: usize,
    lhs: ConstantId<'db>,
    rhs: ConstantId<'db>,
) -> Result<'db> {
    if lhs == rhs {
        Ok(())
    } else {
        Err(Error::NotConvertible)
    }
}

pub fn equate_metavariable_ids<'db>(
    _global: &GlobalEnv<'db>,
    _depth: usize,
    lhs: MetaVariableId,
    rhs: MetaVariableId,
) -> Result<'db> {
    if lhs == rhs {
        Ok(())
    } else {
        Err(Error::NotConvertible)
    }
}

pub fn equate_levels<'db>(
    _global: &GlobalEnv<'db>,
    _depth: usize,
    lhs: Level,
    rhs: Level,
) -> Result<'db> {
    if lhs == rhs {
        Ok(())
    } else {
        Err(Error::NotConvertible)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{MetaVariableId, UniverseLevel};
    use crate::syn::Syntax;
    use crate::val::{GlobalEnv, LocalEnv, Spine};
    use std::rc::Rc;

    // =========================================================================
    // Metavariable Equality Tests
    // =========================================================================

    #[test]
    fn test_equate_metavariable_ids_same() {
        let global = GlobalEnv::new();
        let id = MetaVariableId(0);
        assert!(equate_metavariable_ids(&global, 0, id, id).is_ok());
    }

    #[test]
    fn test_equate_metavariable_ids_different() {
        let global = GlobalEnv::new();
        let id1 = MetaVariableId(0);
        let id2 = MetaVariableId(1);
        assert!(equate_metavariable_ids(&global, 0, id1, id2).is_err());
    }

    #[test]
    fn test_equate_flexes_same_meta_empty_spine() {
        let mut global = GlobalEnv::new();
        let meta_id = MetaVariableId(0);
        global.add_metavariable(meta_id, vec![], Syntax::universe_rc(UniverseLevel::new(0)));

        let u0_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
        let meta_val = val::MetaVariable::new(meta_id, LocalEnv::new());
        let flex1 = val::Flex::new(meta_val.clone(), Spine::empty(), u0_ty.clone());
        let flex2 = val::Flex::new(meta_val, Spine::empty(), u0_ty);

        assert!(equate_flexes(&global, 0, &flex1, &flex2).is_ok());
    }

    #[test]
    fn test_equate_flexes_different_metas() {
        let mut global = GlobalEnv::new();
        let meta_id1 = MetaVariableId(0);
        let meta_id2 = MetaVariableId(1);
        global.add_metavariable(meta_id1, vec![], Syntax::universe_rc(UniverseLevel::new(0)));
        global.add_metavariable(meta_id2, vec![], Syntax::universe_rc(UniverseLevel::new(0)));

        let u0_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
        let flex1 = val::Flex::new(
            val::MetaVariable::new(meta_id1, LocalEnv::new()),
            Spine::empty(),
            u0_ty.clone(),
        );
        let flex2 = val::Flex::new(
            val::MetaVariable::new(meta_id2, LocalEnv::new()),
            Spine::empty(),
            u0_ty,
        );

        assert!(equate_flexes(&global, 0, &flex1, &flex2).is_err());
    }

    #[test]
    fn test_equate_flex_instances() {
        // When a type is a Flex (metavariable), terms should be equal if they're both Flex with same head
        let mut global = GlobalEnv::new();
        let meta_id = MetaVariableId(0);
        global.add_metavariable(meta_id, vec![], Syntax::universe_rc(UniverseLevel::new(0)));

        let u0_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
        let meta_val = val::MetaVariable::new(meta_id, LocalEnv::new());
        let flex_ty = val::Flex::new(meta_val.clone(), Spine::empty(), u0_ty.clone());

        // Two identical Flex values should be equal when typed by a Flex
        let lhs = Value::Flex(flex_ty.clone());
        let rhs = Value::Flex(flex_ty.clone());

        assert!(equate_flex_instances(&global, 0, &lhs, &rhs, &flex_ty).is_ok());
    }

    // =========================================================================
    // Type Equivalence Tests
    // =========================================================================

    #[test]
    fn test_type_equiv_universes() {
        let global = GlobalEnv::new();
        let u0 = Value::universe(UniverseLevel::new(0));
        let u1 = Value::universe(UniverseLevel::new(1));

        // Same universe levels are equivalent
        assert!(type_equiv(&global, 0, &u0, &u0).is_ok());
        assert!(type_equiv(&global, 0, &u1, &u1).is_ok());

        // Different universe levels are not equivalent
        assert!(type_equiv(&global, 0, &u0, &u1).is_err());
    }

    #[test]
    fn test_type_equiv_lift() {
        let global = GlobalEnv::new();
        // Lift types contain hardware types (SLift or MLift)
        // ^$Bit is Lift(SLift(Bit))
        let slift_bit = Rc::new(Value::slift(Rc::new(Value::bit())));
        let lift_bit = Value::lift(slift_bit.clone());
        let lift_bit2 = Value::lift(Rc::new(Value::slift(Rc::new(Value::bit()))));

        // Same lifted types are equivalent
        assert!(type_equiv(&global, 0, &lift_bit, &lift_bit2).is_ok());
    }
}
