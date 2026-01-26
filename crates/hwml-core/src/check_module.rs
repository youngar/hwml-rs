//! Module-level type checking.
//!
//! This module provides functions to type-check declarations and add them to
//! the global environment. It processes declarations in order, allowing later
//! declarations to reference earlier ones.

use crate::check::{check_type, type_check, TCEnvironment};
use crate::declaration::{
    Constant, Declaration, HardwareConstant, HardwarePrimitive, Module, Primitive,
    TypeConstructor as DeclTypeConstructor,
};
use crate::eval;
use crate::syn::{ConstantId, Syntax, Telescope};
use crate::val::{
    ConstantInfo, DataConstructorInfo, GlobalEnv, HardwareConstantInfo, HardwarePrimitiveInfo,
    PrimitiveInfo, TypeConstructorInfo, Value,
};
use std::rc::Rc;

/// Errors that can occur during module checking.
#[derive(Debug, Clone)]
pub enum Error<'db> {
    /// Type checking error for a term.
    TypeCheck(crate::check::Error<'db>),
    /// Evaluation error.
    Eval(crate::eval::Error),
    /// A declaration with this name already exists.
    AlreadyDefined(ConstantId<'db>),
    /// Invalid type constructor universe.
    InvalidTypeConstructorUniverse(ConstantId<'db>),
}

impl<'db> From<crate::check::Error<'db>> for Error<'db> {
    fn from(e: crate::check::Error<'db>) -> Self {
        Error::TypeCheck(e)
    }
}

impl<'db> From<crate::eval::Error> for Error<'db> {
    fn from(e: crate::eval::Error) -> Self {
        Error::Eval(e)
    }
}

/// Result of checking a module.
pub struct CheckedModule<'db> {
    /// The global environment with all checked declarations.
    pub global_env: GlobalEnv<'db>,
    /// Names of constants that have hardware (Lift) types.
    pub hardware_constants: Vec<ConstantId<'db>>,
}

/// Check a module and build a global environment.
///
/// This processes each declaration in order:
/// 1. Type-check the declaration against the current environment
/// 2. Evaluate the value (for constants)
/// 3. Add the declaration to the global environment
/// 4. Track which constants have hardware types (Lift)
pub fn check_module<'db>(
    module: &Module<'db>,
    initial_env: GlobalEnv<'db>,
) -> Result<CheckedModule<'db>, Error<'db>> {
    let mut global_env = initial_env;
    let mut hardware_constants = Vec::new();

    for decl in &module.declarations {
        match decl {
            Declaration::Primitive(prim) => {
                check_primitive(&mut global_env, prim)?;
            }
            Declaration::HardwarePrimitive(hprim) => {
                check_hardware_primitive(&mut global_env, hprim)?;
            }
            Declaration::Constant(constant) => {
                let is_hw = check_constant(&mut global_env, constant)?;
                if is_hw {
                    hardware_constants.push(constant.name);
                }
            }
            Declaration::HardwareConstant(hconst) => {
                check_hardware_constant(&mut global_env, hconst)?;
                hardware_constants.push(hconst.name);
            }
            Declaration::TypeConstructor(tcon) => {
                check_type_constructor(&mut global_env, tcon)?;
            }
        }
    }

    Ok(CheckedModule {
        global_env,
        hardware_constants,
    })
}

/// Check a primitive declaration and add it to the global environment.
fn check_primitive<'db>(
    global: &mut GlobalEnv<'db>,
    prim: &Primitive<'db>,
) -> Result<(), Error<'db>> {
    // Create a type-checking environment
    let mut tc_env = TCEnvironment {
        values: crate::val::Environment::new(global),
        types: Vec::new(),
    };

    // Check that the type is valid
    check_type(&mut tc_env, &prim.ty)?;

    // Add the primitive to the global environment
    global.add_primitive(prim.name, PrimitiveInfo::new(prim.ty.clone()));

    Ok(())
}

/// Check a hardware primitive declaration and add it to the global environment.
///
/// HardwareUniverse primitives differ from regular primitives:
/// - The type must be a hardware type (in Type), not a meta-level type
fn check_hardware_primitive<'db>(
    global: &mut GlobalEnv<'db>,
    hprim: &HardwarePrimitive<'db>,
) -> Result<(), Error<'db>> {
    // Create a type-checking environment
    let mut tc_env = TCEnvironment {
        values: crate::val::Environment::new(global),
        types: Vec::new(),
    };

    // Check that the type is a valid hardware type (has type Type)
    crate::check::check_hwtype_pub(&mut tc_env, &hprim.ty)?;

    // Add the hardware primitive to the global environment
    global.add_hardware_primitive(hprim.name, HardwarePrimitiveInfo::new(hprim.ty.clone()));

    Ok(())
}

/// Check a hardware constant declaration and add it to the global environment.
///
/// HardwareUniverse constants differ from regular constants:
/// - The type must be a hardware type (in Type), not a meta-level type
/// - The value is an HSyntax term, checked using the hardware type checker
fn check_hardware_constant<'db>(
    global: &mut GlobalEnv<'db>,
    hconst: &HardwareConstant<'db>,
) -> Result<(), Error<'db>> {
    // Create a type-checking environment
    let mut tc_env = TCEnvironment {
        values: crate::val::Environment::new(global),
        types: Vec::new(),
    };

    // Check that the type is a valid hardware type (has type Type)
    crate::check::check_hwtype_pub(&mut tc_env, &hconst.ty)?;

    // Evaluate the type to a value
    let mut eval_env = crate::val::Environment::new(global);
    let ty_val = eval::eval(&mut eval_env, &hconst.ty)?;

    // Check the hardware term value against the hardware type
    crate::check::check_hsyntax_pub(&mut tc_env, &hconst.value, &ty_val)?;

    // Add the hardware constant to the global environment
    global.add_hardware_constant(
        hconst.name,
        HardwareConstantInfo::new(hconst.ty.clone(), hconst.value.clone()),
    );

    Ok(())
}

/// Check a constant declaration and add it to the global environment.
/// Returns true if the constant has a hardware type (Lift).
///
/// To support recursive definitions, we add the constant to the environment
/// BEFORE type-checking its body. This allows the body to reference the
/// constant itself. The value is stored as syntax and evaluated on demand
/// (eagerly unfolded during evaluation).
fn check_constant<'db>(
    global: &mut GlobalEnv<'db>,
    constant: &Constant<'db>,
) -> Result<bool, Error<'db>> {
    // Create a type-checking environment
    let mut tc_env = TCEnvironment {
        values: crate::val::Environment::new(global),
        types: Vec::new(),
    };

    // Check that the type is valid (doesn't need the constant itself)
    check_type(&mut tc_env, &constant.ty)?;

    // Evaluate the type to a value
    let mut eval_env = crate::val::Environment::new(global);
    let ty_val = eval::eval(&mut eval_env, &constant.ty)?;

    // Check if this is a hardware constant (has a Lift type or is a closed hardware type)
    let is_hardware = is_hardware_type(&ty_val);

    // Add the constant to the global environment BEFORE checking the body.
    // This enables recursive definitions - the body can reference the constant.
    // The value is stored as syntax (not pre-evaluated).
    global.add_constant(
        constant.name,
        ConstantInfo::new(constant.ty.clone(), constant.value.clone()),
    );

    // Create a fresh type-checking environment that includes the new constant
    let mut tc_env = TCEnvironment {
        values: crate::val::Environment::new(global),
        types: Vec::new(),
    };

    // Check that the value has the declared type.
    // If the body references the constant recursively, eval_constant will
    // unfold it by evaluating the syntax.
    type_check(&mut tc_env, &constant.value, &ty_val)?;

    Ok(is_hardware)
}

/// Check a type constructor declaration and add it to the global environment.
fn check_type_constructor<'db>(
    global: &mut GlobalEnv<'db>,
    tcon: &DeclTypeConstructor<'db>,
) -> Result<(), Error<'db>> {
    // Parse the universe from the declaration
    // The universe syntax should be something like "U0", "U1", etc.
    let level = match tcon.universe.as_ref() {
        Syntax::Universe(u) => u.level,
        _ => return Err(Error::InvalidTypeConstructorUniverse(tcon.name)),
    };

    // For now, we treat all arguments as parameters (no indices)
    // TODO: Properly parse parameters vs indices from the declaration
    let arguments: Telescope<'db> = [].into();
    let num_parameters = 0;

    // Add the type constructor to the global environment
    global.add_type_constructor(
        tcon.name,
        TypeConstructorInfo::new(arguments, num_parameters, level),
    );

    // Add each data constructor
    for dcon in &tcon.data_constructors {
        global.add_data_constructor(
            dcon.name,
            DataConstructorInfo::new(dcon.parameters.clone(), dcon.result_type.clone()),
        );
    }

    Ok(())
}

/// Determine if a type represents a hardware-level constant.
///
/// HardwareUniverse constants have types that:
/// - Are `Lift` types (^ht)
/// - Are Pi types that eventually return a Lift type
///
/// For Pi types, we check the syntax of the target closure's body,
/// since closures contain unevaluated syntax.
fn is_hardware_type(ty: &Value) -> bool {
    match ty {
        // Direct Lift type: ^ht
        Value::Lift(_) => true,

        // Pi type: check if the final return type is hardware
        // We need to check the syntax of the closure body
        Value::Pi(pi) => is_hardware_type_syntax(&pi.target.term),

        // Everything else is meta-level
        _ => false,
    }
}

/// Check if syntax represents a hardware type.
fn is_hardware_type_syntax<'db>(ty: &Syntax<'db>) -> bool {
    match ty {
        // Lift type in syntax
        Syntax::Lift(_) => true,

        // Pi type: check the target
        Syntax::Pi(pi) => is_hardware_type_syntax(&pi.target),

        // Check term - recurse into the inner term
        Syntax::Check(check) => is_hardware_type_syntax(&check.term),

        // Everything else is not hardware
        _ => false,
    }
}

/// Extract the inner hardware type from a Lift type.
/// Returns None if the type is not a Lift.
pub fn extract_lift_inner_type<'a, 'db>(ty: &'a Value<'db>) -> Option<&'a Rc<Value<'db>>> {
    match ty {
        Value::Lift(inner) => Some(inner),
        _ => None,
    }
}
