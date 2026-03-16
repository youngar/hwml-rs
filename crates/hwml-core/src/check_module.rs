//! Module-level type checking.
//!
//! This module provides functions to type-check declarations and add them to
//! the global environment. It processes declarations in order, allowing later
//! declarations to reference earlier ones.

use crate::check::{check_type, type_check, TCEnvironment};
use crate::eval;
use crate::syn::declaration::{
    CompilationUnit, ConstantDecl, DataConstructorDecl, Declaration, MetavariableDecl,
    PrimitiveDecl, TypeConstructorDecl,
};
use crate::syn::{Syntax, Telescope};
use crate::val::{
    ConstantInfo, DataConstructorInfo, GlobalEnv, PrimitiveInfo, TypeConstructorInfo, Value,
};
use crate::{QualifiedName, RcValue};
use salsa::Database;
use std::rc::Rc;

/// Errors that can occur during module checking.
#[derive(Debug, Clone)]
pub enum Error<'db> {
    /// Type checking error for a term.
    TypeCheck(crate::check::Error<'db>),
    /// Evaluation error.
    Eval(crate::eval::Error),
    /// A declaration with this name already exists.
    AlreadyDefined(QualifiedName<'db>),
    /// Invalid type constructor universe.
    InvalidTypeConstructorUniverse(QualifiedName<'db>),
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
    pub hardware_constants: Vec<QualifiedName<'db>>,
}

/// Check a module in two passes: first add all declarations to the environment,
/// then validate them. This allows mutual recursion between all global declarations.
pub fn check_module<'db>(
    db: &'db dyn Database,
    module: &CompilationUnit<'db>,
    initial_env: GlobalEnv<'db>,
) -> Result<CheckedModule<'db>, Error<'db>> {
    let mut global_env = initial_env;

    // Add all declarations to the environment
    for decl in &module.declarations {
        match decl {
            Declaration::PrimitiveDecl(prim) => add_primitive_to_env(&mut global_env, prim),
            Declaration::ConstantDecl(constant) => add_constant_to_env(&mut global_env, constant),
            Declaration::TypeConstructorDecl(tcon) => {
                add_type_constructor_to_env(&mut global_env, tcon)?
            }
            Declaration::MetavariableDecl(meta) => add_metavariable_to_env(&mut global_env, meta),
        }
    }

    // Validate all declarations
    let mut hardware_constants = Vec::new();
    for decl in &module.declarations {
        match decl {
            Declaration::PrimitiveDecl(prim) => validate_primitive(db, &global_env, prim)?,
            Declaration::ConstantDecl(constant) => {
                let is_hw = validate_constant(db, &global_env, constant)?;
                if is_hw {
                    hardware_constants.push(constant.name);
                }
            }
            Declaration::TypeConstructorDecl(tcon) => {
                validate_type_constructor(db, &global_env, tcon)?
            }
            Declaration::MetavariableDecl(meta) => validate_metavariable(db, &global_env, meta)?,
        }
    }

    Ok(CheckedModule {
        global_env,
        hardware_constants,
    })
}

fn add_primitive_to_env<'db>(global: &mut GlobalEnv<'db>, prim: &PrimitiveDecl<'db>) {
    global.add_primitive(prim.name, PrimitiveInfo::new(prim.ty.clone()));
}

fn validate_primitive<'db>(
    db: &'db dyn Database,
    global: &GlobalEnv<'db>,
    prim: &PrimitiveDecl<'db>,
) -> Result<(), Error<'db>> {
    let mut tc_env = TCEnvironment {
        db,
        values: crate::val::Environment::new(global),
        types: Vec::new(),
    };
    check_type(&mut tc_env, &prim.ty)?;
    Ok(())
}

fn add_constant_to_env<'db>(global: &mut GlobalEnv<'db>, constant: &ConstantDecl<'db>) {
    global.add_constant(
        constant.name,
        ConstantInfo::new(constant.ty.clone(), constant.value.clone()),
    );
}

fn validate_constant<'db>(
    db: &'db dyn Database,
    global: &GlobalEnv<'db>,
    constant: &ConstantDecl<'db>,
) -> Result<bool, Error<'db>> {
    let mut tc_env = TCEnvironment {
        db,
        values: crate::val::Environment::new(global),
        types: Vec::new(),
    };

    check_type(&mut tc_env, &constant.ty)?;

    let mut eval_env = crate::val::Environment::new(global);
    let ty_val = eval::eval(&mut eval_env, &constant.ty)?;

    let is_hardware = is_hardware_type(&ty_val);
    type_check(&mut tc_env, &constant.value, &ty_val)?;

    Ok(is_hardware)
}

fn add_type_constructor_to_env<'db>(
    global: &mut GlobalEnv<'db>,
    tcon: &TypeConstructorDecl<'db>,
) -> Result<(), Error<'db>> {
    let level = match tcon.universe.as_ref() {
        Syntax::Universe(u) => u.level,
        _ => return Err(Error::InvalidTypeConstructorUniverse(tcon.name)),
    };

    let num_parameters = tcon.parameters.len();
    let mut all_types: Vec<_> = tcon.parameters.iter().cloned().collect();
    all_types.extend(tcon.indices.iter().cloned());
    let arguments = Telescope::new(all_types);

    let dcon_names: Vec<_> = tcon.data_constructors.iter().map(|d| d.name).collect();

    let mut tcon_info = TypeConstructorInfo::new(arguments.clone(), num_parameters, level);
    tcon_info.constructors = dcon_names;
    global.add_type_constructor(tcon.name, tcon_info);

    for dcon in &tcon.data_constructors {
        global.add_data_constructor(
            dcon.name,
            DataConstructorInfo::new(dcon.parameters.clone(), dcon.result_type.clone()),
        );
    }

    Ok(())
}

fn validate_type_constructor<'db>(
    db: &'db dyn Database,
    global: &GlobalEnv<'db>,
    tcon: &TypeConstructorDecl<'db>,
) -> Result<(), Error<'db>> {
    let mut tc_env = TCEnvironment {
        db,
        values: crate::val::Environment::new(global),
        types: Vec::new(),
    };

    check_type(&mut tc_env, &tcon.universe)?;
    let universe_ty = crate::check::type_synth(&mut tc_env, &tcon.universe)?;
    let Value::Universe(tcon_universe) = &*universe_ty else {
        return Err(Error::InvalidTypeConstructorUniverse(tcon.name));
    };

    for param_ty in tcon.parameters.iter() {
        check_type(&mut tc_env, param_ty)?;
        let param_ty_val = eval::eval(&mut tc_env.values, param_ty)?;
        tc_env.push_var(param_ty_val);
    }

    for index_ty in tcon.indices.iter() {
        check_type(&mut tc_env, index_ty)?;
        let index_ty_val = eval::eval(&mut tc_env.values, index_ty)?;
        tc_env.push_var(index_ty_val);
    }

    for dcon in tcon.data_constructors.iter() {
        validate_data_constructor(db, global, tcon, tcon_universe, dcon)?;
    }

    Ok(())
}

fn validate_data_constructor<'db>(
    db: &'db dyn Database,
    global: &GlobalEnv<'db>,
    tcon: &TypeConstructorDecl<'db>,
    _tcon_universe: &crate::val::Universe<'db>,
    dcon: &DataConstructorDecl<'db>,
) -> Result<(), Error<'db>> {
    let mut tc_env = TCEnvironment {
        db,
        values: crate::val::Environment::new(global),
        types: Vec::new(),
    };

    // Add type constructor parameters (but not indices) to match parser scoping.
    for param_ty in tcon.parameters.iter() {
        let param_ty_val = eval::eval(&mut tc_env.values, param_ty)?;
        tc_env.push_var(param_ty_val);
    }

    // Validate data constructor parameters.
    for param_ty in dcon.parameters.iter() {
        check_type(&mut tc_env, param_ty)?;
        let param_ty_val = eval::eval(&mut tc_env.values, param_ty)?;
        tc_env.push_var(param_ty_val);
    }

    check_type(&mut tc_env, &dcon.result_type)?;

    // TODO: strict positivity and universe level checking

    Ok(())
}

fn add_metavariable_to_env<'db>(global: &mut GlobalEnv<'db>, meta: &MetavariableDecl<'db>) {
    global.add_metavariable(meta.id, meta.arguments.clone(), meta.ty.clone());
}

fn validate_metavariable<'db>(
    db: &'db dyn Database,
    global: &GlobalEnv<'db>,
    meta: &MetavariableDecl<'db>,
) -> Result<(), Error<'db>> {
    let mut tc_env = TCEnvironment {
        db,
        values: crate::val::Environment::new(global),
        types: Vec::new(),
    };

    for arg_ty in meta.arguments.iter() {
        check_type(&mut tc_env, arg_ty)?;
        let arg_ty_val = eval::eval(&mut tc_env.values, arg_ty)?;
        tc_env.push_var(arg_ty_val);
    }

    check_type(&mut tc_env, &meta.ty)?;
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
fn is_hardware_type_syntax<'db>(ty: &Rc<Syntax<'db>>) -> bool {
    match ty.as_ref() {
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
pub fn extract_lift_inner_type<'a, 'db>(ty: &'a Value<'db>) -> Option<&'a RcValue<'db>> {
    match ty {
        Value::Lift(lift) => Some(&lift.ty),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syn::parse::parse_module;
    use crate::Database;

    #[test]
    fn test_check_dependent_metavariable() {
        // Test that dependent metavariables are parsed and type-checked correctly.
        // A dependent metavariable: ?[0] : (A : U0) -> A -> U0
        // The type of the second argument (%x : %A) references the first argument.
        let db = Database::default();
        let input = "prim $Nat : U0; meta ?[0] (%A : U0) (%x : %A) : U0;";
        let module = parse_module(&db, input).expect("Failed to parse module");
        let result = check_module(&db, &module, GlobalEnv::new());
        assert!(
            result.is_ok(),
            "Dependent metavariable should type-check: {:?}",
            result.err()
        );
    }
}
