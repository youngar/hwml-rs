//! Module-level type checking.
//!
//! This module provides functions to type-check declarations and add them to
//! the global environment. It processes declarations in order, allowing later
//! declarations to reference earlier ones.

use crate::check::{check_type, type_check, TCEnvironment};
use crate::eval;
use syn::declaration::{
    CompilationUnit, ConstantDecl, DataConstructorDecl, Declaration, MetavariableDecl,
    PrimitiveDecl, TypeConstructorDecl,
};
use syn::{RcSyntax, Syntax, Telescope};
use val::{
    ConstantInfo, DataConstructorInfo, GlobalEnv, PrimitiveInfo, TypeConstructorInfo, Value,
};
use crate::*;
use crate::{QualifiedName, RcValue};
use salsa::Database;

/// Errors that can occur during module checking.
#[derive(Debug, Clone)]
pub enum Error<'db> {
    /// Type checking error for a term.
    TypeCheck(crate::check::Error<'db>),
    /// Evaluation error.
    Eval(crate::eval::Error<'db>),
    /// A declaration with this name already exists.
    AlreadyDefined(QualifiedName<'db>),
    /// Invalid type constructor universe.
    InvalidTypeConstructorUniverse(QualifiedName<'db>),
}

impl<'db> From<check::Error<'db>> for Error<'db> {
    fn from(e: check::Error<'db>) -> Self {
        Error::TypeCheck(e)
    }
}

impl<'db> From<eval::Error<'db>> for Error<'db> {
    fn from(e: eval::Error<'db>) -> Self {
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
        values: val::Environment::new(global),
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
        values: val::Environment::new(global),
        types: Vec::new(),
    };

    check_type(&mut tc_env, &constant.ty)?;

    let mut eval_env = val::Environment::new(global);
    let ty_val_code = eval::eval(&mut eval_env, &constant.ty)?;
    let ty_val = crate::eval::decode_type_code(global, &ty_val_code)?;

    let is_hardware = is_hardware_type(&ty_val_code);
    type_check(&mut tc_env, &constant.value, &ty_val)?;

    Ok(is_hardware)
}

fn add_type_constructor_to_env<'db>(
    global: &mut GlobalEnv<'db>,
    tcon: &TypeConstructorDecl<'db>,
) -> Result<(), Error<'db>> {
    // Extract universe level from the target type (syn::RcTy).
    // With type-aware syntax, this is El(UniverseCode(level)) or El(Check(UniverseCode(level), ...))
    use syn::Ty;
    let level = match tcon.target.as_ref() {
        Ty::El(code) => match code.as_ref() {
            Syntax::UniverseCode(level) => *level,
            Syntax::Check(check) => match check.term.as_ref() {
                Syntax::UniverseCode(level) => *level,
                _ => return Err(Error::InvalidTypeConstructorUniverse(tcon.name)),
            },
            _ => return Err(Error::InvalidTypeConstructorUniverse(tcon.name)),
        },
        _ => return Err(Error::InvalidTypeConstructorUniverse(tcon.name)),
    };

    let num_parameters = tcon.parameters.len();
    let mut all_types: Vec<_> = tcon.parameters.iter().cloned().collect();
    all_types.extend(tcon.indices.iter().cloned());
    let arguments = Telescope::new(all_types);

    let dcon_names: Vec<_> = tcon.data_constructors.iter().map(|d| d.name).collect();

    let mut tcon_info =
        TypeConstructorInfo::new(arguments.clone(), num_parameters, UniverseLevel::new(level));
    tcon_info.constructors = dcon_names;
    global.add_type_constructor(tcon.name, tcon_info);

    for dcon in &tcon.data_constructors {
        global.add_data_constructor(
            dcon.name,
            DataConstructorInfo::new(dcon.parameters.clone(), dcon.target.clone()),
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
        values: val::Environment::new(global),
        types: Vec::new(),
    };

    // The target field is now a syn::RcTy - validate it with check_ty
    crate::check::check_ty(&mut tc_env, &tcon.target)?;

    // Extract the universe level from the type (El(UniverseCode(...)) or El(Check(UniverseCode(...), ...)))
    use syn::Ty;
    let tcon_universe_level = match tcon.target.as_ref() {
        Ty::El(code) => match code.as_ref() {
            Syntax::UniverseCode(level) => *level,
            Syntax::Check(check) => match check.term.as_ref() {
                Syntax::UniverseCode(level) => *level,
                _ => return Err(Error::InvalidTypeConstructorUniverse(tcon.name)),
            },
            _ => return Err(Error::InvalidTypeConstructorUniverse(tcon.name)),
        },
        _ => return Err(Error::InvalidTypeConstructorUniverse(tcon.name)),
    };

    for param_binder in tcon.parameters.iter() {
        check_type(&mut tc_env, &param_binder.ty)?;
        let param_ty_val_code = eval::eval(&mut tc_env.values, &param_binder.ty)?;
        let param_ty_val = crate::eval::decode_type_code(global, &param_ty_val_code)?;
        tc_env.push_var(param_ty_val);
    }

    for index_binder in tcon.indices.iter() {
        check_type(&mut tc_env, &index_binder.ty)?;
        let index_ty_val_code = eval::eval(&mut tc_env.values, &index_binder.ty)?;
        let index_ty_val = crate::eval::decode_type_code(global, &index_ty_val_code)?;
        tc_env.push_var(index_ty_val);
    }

    for dcon in tcon.data_constructors.iter() {
        validate_data_constructor(db, global, tcon, tcon_universe_level, dcon)?;
    }

    Ok(())
}

fn validate_data_constructor<'db>(
    db: &'db dyn Database,
    global: &GlobalEnv<'db>,
    tcon: &TypeConstructorDecl<'db>,
    _tcon_universe_level: usize,
    dcon: &DataConstructorDecl<'db>,
) -> Result<(), Error<'db>> {
    let mut tc_env = TCEnvironment {
        db,
        values: val::Environment::new(global),
        types: Vec::new(),
    };

    // Add type constructor parameters (but not indices) to match parser scoping.
    for param_binder in tcon.parameters.iter() {
        let param_ty_val_code = eval::eval(&mut tc_env.values, &param_binder.ty)?;
        let param_ty_val = crate::eval::decode_type_code(global, &param_ty_val_code)?;
        tc_env.push_var(param_ty_val);
    }

    // Validate data constructor parameters.
    for param_binder in dcon.parameters.iter() {
        check_type(&mut tc_env, &param_binder.ty)?;
        let param_ty_val_code = eval::eval(&mut tc_env.values, &param_binder.ty)?;
        let param_ty_val = crate::eval::decode_type_code(global, &param_ty_val_code)?;
        tc_env.push_var(param_ty_val);
    }

    check_type(&mut tc_env, &dcon.target)?;

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
        values: val::Environment::new(global),
        types: Vec::new(),
    };

    for arg_binder in meta.arguments.iter() {
        check_type(&mut tc_env, &arg_binder.ty)?;
        let arg_ty_val_code = eval::eval(&mut tc_env.values, &arg_binder.ty)?;
        let arg_ty_val = crate::eval::decode_type_code(global, &arg_ty_val_code)?;
        tc_env.push_var(arg_ty_val);
    }

    check_type(&mut tc_env, &meta.ty)?;
    Ok(())
}

/// Determine if a type represents a hardware-level constant.
///
/// HardwareUniverse constants have types that:
/// - Are `SLift` types (Sig s - signal types wrapped to hardware)
/// - Are `MLift` types (Mod m - module types wrapped to hardware)
/// - Are PiCode types that eventually return a hardware type
///
/// For PiCode types, we check the syntax of the target closure's body,
/// since closures contain unevaluated syntax.
fn is_hardware_type(ty: &Value) -> bool {
    match ty {
        // SLift and MLift are hardware types
        Value::SLift(_) | Value::MLift(_) => true,

        // PiCode type: check if the final return type is hardware
        // We need to check the syntax of the closure body
        Value::PiCode(_, _icit, target) => is_hardware_type_syntax(&target.term),

        // Everything else is meta-level
        _ => false,
    }
}

/// Check if syntax represents a hardware type.
fn is_hardware_type_syntax<'db>(ty: &RcSyntax<'db>) -> bool {
    match ty.as_ref() {
        // SLift and MLift types in syntax
        Syntax::SLift(_) | Syntax::MLift(_) => true,

        // PiCode type: check the target
        Syntax::PiCode(_, _icit, target) => is_hardware_type_syntax(&target.body),

        // Check term - recurse into the inner term
        Syntax::Check(check) => is_hardware_type_syntax(&check.term),

        // Everything else is not hardware
        _ => false,
    }
}

/// Extract the inner hardware type from an SLift or MLift type.
/// Returns None if the type is not a hardware lift.
pub fn extract_lift_inner_type<'a, 'db>(ty: &'a Value<'db>) -> Option<&'a RcValue<'db>> {
    match ty {
        Value::SLift(slift) => Some(&slift.ty),
        Value::MLift(mlift) => Some(&mlift.ty),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use syn::parse::parse_module;
    use crate::TestDatabase;

    #[test]
    fn test_check_dependent_metavariable() {
        // Test that dependent metavariables are parsed and type-checked correctly.
        // A dependent metavariable: ?[0] : (A : U0) -> A -> U0
        // The type of the second argument (%x : %A) references the first argument.
        let db = TestDatabase::default();
        // **PHASE 9**: Universe codes are check-only, so we need type annotations
        let input = "prim $Nat : (U0 : UniverseType); meta ?[0] (%A : (U0 : UniverseType)) (%x : %A) : (U0 : UniverseType);";
        let module = parse_module(&db, input).expect("Failed to parse module");
        let result = check_module(&db, &module, GlobalEnv::new(&db));
        assert!(
            result.is_ok(),
            "Dependent metavariable should type-check: {:?}",
            result.err()
        );
    }
}
