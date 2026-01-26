use crate::common::Level;
use crate::eval::{self, eval_telescope};
use crate::syn::{CaseBranch, ConstantId, RcSyntax, RcSyntax, Syntax, Syntax};
use crate::val::{self, Closure, Eliminator, Environment, Flex, LocalEnv, Rigid};
use crate::val::{GlobalEnv, Normal, Value, Value};
use std::rc::Rc;

/// A quotation error.
#[derive(Debug, Clone)]
pub enum Error<'db> {
    /// Something about the input was ill-typed, preventing quotation.
    IllTyped,
    /// Quotation can force evaluation, which may itself prevent an error.
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

/// Read a normal (value * type) back into syntax. The resulting syntax is in normal form.
pub fn quote_normal<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    normal: &Normal<'db>,
) -> Result<'db, RcSyntax<'db>> {
    quote(db, global, depth, &normal.ty, &normal.value)
}

/// Read a value back into syntax. The resulting syntax is in normal form.
/// Quotation is a type-directed procedure whereby we convert a value in the
/// semantic domain to a syntactic normal form.
pub fn quote<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    ty: &Value<'db>,
    value: &Value<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match ty {
        Value::Pi(pi) => quote_pi_instance(db, global, depth, pi, value),
        Value::Universe(universe) => quote_universe_instance(db, global, depth, universe, value),
        Value::TypeConstructor(tc) => quote_type_constructor_instance(db, global, depth, tc, value),
        Value::Rigid(rigid) => quote_rigid_instance(db, global, depth, rigid, value),
        Value::Flex(flex) => quote_flex_instance(db, global, depth, flex, value),
        // HardwareUniverse types
        Value::Type(_) => quote_hwtype(db, global, depth, value),
        Value::Lift(hw_ty) => quote_lift_instance(db, global, depth, hw_ty, value),

        // These are not valid types at meta level
        Value::Bit
        | Value::HArrow(_)
        | Value::Quote(_)
        | Value::Constant(_)
        | Value::Lambda(_)
        | Value::DataConstructor(_) => Err(Error::IllTyped),
        _ => Err(Error::IllTyped),
    }
}

/// Read an instance of a pi type back to syntax.
fn quote_pi_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    ty: &val::Pi<'db>,
    value: &Value<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Build a variable representing the lambda's argument.
    let var = Rc::new(Value::variable(Level::new(depth), ty.source.clone()));

    // Compute the body type by substituting the variable into the target type.
    let body_ty = match eval::run_closure(global, &ty.target, [var.clone()]) {
        Ok(body_ty) => body_ty,
        Err(error) => return Err(Error::EvalError(error)),
    };

    // Compute the body value. This will error if the value is not a lambda.
    let body = match eval::run_application(global, value, var) {
        Ok(body_ty) => body_ty,
        Err(eval_error) => return Err(Error::EvalError(eval_error)),
    };

    // Now quote the body back to syntax.
    let body_stx = quote(db, global, depth + 1, &body_ty, &body)?;

    // Build and return the lambda.
    let lam = Syntax::lambda(body_stx);
    Ok(Rc::new(lam))
}

/// Read an instance of a universe back to syntax.
fn quote_universe_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    _: &val::Universe,
    value: &Value<'db>,
) -> Result<'db, RcSyntax<'db>> {
    quote_type(db, global, depth, value)
}

/// Read an instance of a datatype back to syntax.
fn quote_type_constructor_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    ty: &val::TypeConstructor<'db>,
    value: &Value<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::DataConstructor(data_constructor) => {
            quote_data_constructor(db, global, depth, ty, data_constructor)
        }
        Value::Rigid(rigid) => quote_rigid(db, global, depth, rigid),
        Value::Flex(flex) => quote_flex(db, global, depth, flex),
        Value::Prim(name) => quote_prim(*name),
        _ => Err(Error::IllTyped),
    }
}

fn quote_rigid_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    _ty: &val::Rigid<'db>,
    value: &Value<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::Rigid(rigid) => quote_rigid(db, global, depth, rigid),
        Value::Prim(name) => quote_prim(*name),
        _ => Err(Error::IllTyped),
    }
}

fn quote_flex_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    _ty: &val::Flex<'db>,
    value: &Value<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::Flex(flex) => quote_flex(db, global, depth, flex),
        Value::Prim(name) => quote_prim(*name),
        _ => Err(Error::IllTyped),
    }
}

/// Read back a type in the semantic domain into a syntactic type.
pub fn quote_type<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::Pi(pi) => quote_pi(db, global, depth, pi),
        Value::TypeConstructor(tc) => quote_type_constructor(db, global, depth, tc),
        Value::Universe(universe) => quote_universe(db, depth, universe),
        // HardwareUniverse types that can appear as meta-level types
        Value::Lift(hw_ty) => {
            let hw_ty_stx = quote_hwtype(db, global, depth, hw_ty)?;
            Ok(Syntax::lift_rc(hw_ty_stx))
        }

        _ => Err(Error::IllTyped),
    }
}

// ============================================================================
// HardwareUniverse Quotation
// ============================================================================

/// Quote a hardware type (value of type Type) back to syntax.
fn quote_hwtype<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::Bit => Ok(Syntax::bit_rc()),
        Value::HArrow(harrow) => {
            let source = quote_hwtype(db, global, depth, &harrow.source)?;
            let target = quote_hwtype(db, global, depth, &harrow.target)?;
            Ok(Syntax::harrow_rc(source, target))
        }
        Value::Rigid(rigid) => quote_rigid(db, global, depth, rigid),
        Value::Flex(flex) => quote_flex(db, global, depth, flex),
        Value::Prim(name) => quote_prim(*name),
        _ => Err(Error::IllTyped),
    }
}

/// Quote an instance of a lifted type (^ht) back to syntax.
fn quote_lift_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    hw_ty: &Value<'db>,
    value: &Value<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match value {
        Value::Quote(hw_value) => {
            // Quote the hardware value back to syntax using type-directed quotation
            let hw_syntax = quote_Value(db, global, depth, hw_ty, hw_value)?;
            Ok(Syntax::quote_rc(hw_syntax))
        }
        Value::Rigid(rigid) => quote_rigid(db, global, depth, rigid),
        Value::Flex(flex) => quote_flex(db, global, depth, flex),
        Value::Prim(name) => quote_prim(*name),
        _ => Err(Error::IllTyped),
    }
}

/// Quote a hardware value back to hardware syntax.
/// This is the type-directed readback function for the hardware value domain.
///
/// Type-directed quotation means we dispatch based on the *type* of the value,
/// not the value itself. This is essential for correctly handling functions:
/// - For `HArrow(source, target)`, we apply the value to a fresh variable
/// - For `Bit`, we just quote the canonical value
fn quote_Value<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    hw_ty: &Value<'db>,
    Value: &Value<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match hw_ty {
        // Function type: apply to fresh variable and quote the result
        Value::HArrow(harrow) => quote_harrow_instance(db, global, depth, harrow, Value),

        // Base type (Bit): quote the value directly
        Value::Bit => quote_Value_at_base(depth, Value),

        // Neutral types: quote the value directly
        Value::Rigid(_) | Value::Flex(_) => quote_Value_at_base(depth, Value),

        // Invalid types at hardware level
        _ => Err(Error::IllTyped),
    }
}

/// Quote an instance of a hardware arrow type (a -> b) back to syntax.
/// This is analogous to quote_pi_instance for meta-level functions.
fn quote_harrow_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    harrow: &val::HArrow<'db>,
    Value: &Value<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Create a fresh hardware variable at the current depth
    let fresh_var = Rc::new(Value::hvariable(Level::new(depth)));

    // Apply the hardware value to this fresh variable
    let body_value = eval::apply_Value(global, Value, fresh_var)?;

    // Quote the body at depth + 1, with the target type
    let body_syntax = quote_Value(db, global, depth + 1, &harrow.target, &body_value)?;

    // Build and return the lambda
    Ok(Rc::new(Syntax::Module(body_syntax)))
}

/// Quote a hardware value at a base type (not a function type).
/// This handles the non-type-directed cases where we just inspect the value.
fn quote_Value_at_base<'db>(depth: usize, Value: &Value<'db>) -> Result<'db, RcSyntax<'db>> {
    match Value {
        // Canonical bit values
        Value::Zero => Ok(Rc::new(Syntax::zero())),
        Value::One => Ok(Rc::new(Syntax::one())),

        // HardwareUniverse variable - convert level to index
        Value::HVariable(var) => {
            let index = var.level.to_index(depth);
            Ok(Rc::new(Syntax::hvariable(index)))
        }

        // Embedded meta-level neutral - wrap back in Splice syntax
        Value::Splice(term) => Ok(Rc::new(Syntax::splice(term.clone()))),

        // HardwareUniverse constant reference
        Value::HConstant(name) => Ok(Rc::new(Syntax::hconstant(*name))),

        // HardwareUniverse primitive reference
        Value::HPrim(name) => Ok(Rc::new(Syntax::hprim(*name))),

        // Lambda at base type - this shouldn't happen if types are correct
        // But we handle it for robustness by quoting it untyped
        Value::Module(closure) => {
            // This is a type error in principle, but we try to recover
            // by just returning the closure body (which may have wrong indices)
            Ok(Rc::new(Syntax::Module(closure.body.clone())))
        }

        // Neutral application
        Value::HApp(fun, arg) => {
            let fun_syn = quote_Value_at_base(depth, fun)?;
            let arg_syn = quote_Value_at_base(depth, arg)?;
            Ok(Rc::new(Syntax::happlication(fun_syn, arg_syn)))
        }
    }
}

/// Quote a hardware value back to hardware syntax without type information.
///
/// This is a convenience function for callers who don't have access to the
/// hardware type. It performs non-type-directed quotation, which may not
/// correctly handle hardware lambdas (they will be quoted with potentially
/// incorrect de Bruijn indices).
///
/// For correct quotation of hardware functions, use `quote_Value` with the
/// hardware type.
pub fn quote_hardware<'db>(depth: usize, Value: &Value<'db>) -> Result<'db, RcSyntax<'db>> {
    quote_Value_at_base(depth, Value)
}

// Read a pi back to syntax.
fn quote_pi<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    sem_pi: &val::Pi<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Read back the source type.
    let sem_source_ty = &sem_pi.source;
    let syn_source_ty = quote_type(db, global, depth, sem_source_ty)?;

    // Read back the target type.
    let var = Rc::new(Value::variable(Level::new(depth), sem_pi.source.clone()));
    let sem_target_ty = match eval::run_closure(global, &sem_pi.target, [var]) {
        Ok(ty) => ty,
        Err(error) => return Err(Error::EvalError(error)),
    };
    let syn_target_ty = quote_type(db, global, depth + 1, &sem_target_ty)?;

    // Return the syntactic pi.
    let syn_pi = Syntax::pi(syn_source_ty, syn_target_ty);
    Ok(Rc::new(syn_pi))
}

/// Read a data constructor instance back to syntax.
fn quote_type_constructor<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    sem_tcon: &val::TypeConstructor<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Get the constructor constant.
    let constructor = sem_tcon.constructor;

    // Look up the type info.
    let type_info: val::TypeConstructorInfo<'db> = global
        .type_constructor(constructor)
        .map_err(Error::LookupError)?
        .clone();

    // Create a new environment.
    let mut env = Environment {
        global: global,
        local: LocalEnv::new(),
    };

    // The arguments vector contains parameters first, then indices.
    let mut arguments = Vec::new();

    // Quote each argument (both parameters and indices).
    for (sem_arg, syn_ty) in sem_tcon.iter().zip(type_info.arguments.iter()) {
        // Evaluate the type of the current argument.
        let sem_ty = eval::eval(&mut env, &syn_ty).map_err(Error::EvalError)?;

        // Quote the current argument.
        let syn_arg = quote(db, global, depth, &sem_ty, sem_arg)?;
        arguments.push(syn_arg);

        // Push the semantic argument into the environment for subsequent iterations.
        env.push(sem_arg.clone());
    }
    Ok(Syntax::type_constructor_rc(constructor, arguments))
}

/// Read a universe back to syntax.
fn quote_universe<'db>(
    _db: &'db dyn salsa::Database,
    _depth: usize,
    sem_universe: &val::Universe,
) -> Result<'db, RcSyntax<'db>> {
    // Return a syntactic universe at the same universe level.
    let syn_universe = Syntax::universe(sem_universe.level);
    Ok(Rc::new(syn_universe))
}

/// Read a rigid neutral back to syntax by quoting the head and traversing the spine.
fn quote_rigid<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    rigid: &Rigid<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Start with the variable at the head.
    let mut result = quote_variable(db, depth, &rigid.head)?;

    // Traverse the spine, applying each eliminator.
    for eliminator in rigid.spine.iter() {
        result = quote_eliminator(db, global, depth, result, eliminator)?;
    }

    Ok(result)
}

/// Read a flexible neutral back to syntax by quoting the head and traversing the spine.
fn quote_flex<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    flex: &Flex<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Quote the metavariable head by converting its local environment to a closure.
    let mut result = quote_metavariable(db, global, depth, &flex.head)?;

    // Traverse the spine, applying each eliminator.
    for eliminator in flex.spine.iter() {
        result = quote_eliminator(db, global, depth, result, eliminator)?;
    }

    Ok(result)
}

/// Quote a primitive reference back to syntax.
/// Primitives are neutral values - they have no definition to unfold.
fn quote_prim<'db>(name: ConstantId<'db>) -> Result<'db, RcSyntax<'db>> {
    Ok(Rc::new(Syntax::prim(name)))
}

/// Quote an eliminator applied to a term.
fn quote_eliminator<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    head: RcSyntax<'db>,
    eliminator: &Eliminator<'db>,
) -> Result<'db, RcSyntax<'db>> {
    match eliminator {
        Eliminator::Application(app) => {
            // Quote the argument.
            let syn_arg = quote_normal(db, global, depth, &app.argument)?;
            // Build the application.
            let syn_app = Syntax::application(head, syn_arg);
            Ok(Rc::new(syn_app))
        }
        Eliminator::Case(case) => {
            // Quote the case eliminator.
            quote_case_eliminator(db, global, depth, head, case)
        }
    }
}

/// Read a data constructor instance back to syntax.
fn quote_data_constructor<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    mut depth: usize,
    type_constructor: &val::TypeConstructor<'db>,
    sem_data: &val::DataConstructor<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Get the constructor constant.
    let constructor = sem_data.constructor;

    // Look up the type constructor info (from the type, not the data constructor).
    let type_info = global
        .type_constructor(type_constructor.constructor)
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
    let parameters = type_constructor.iter().take(num_parameters).cloned();

    // Create an environment for evaluating the type of each argument, with
    // parameters in the context.
    let mut env = Environment {
        global: global,
        local: LocalEnv::new(),
    };
    env.extend(parameters);
    // TODO: i don't think we should be adding the parameters to the depth here...
    // we use the depth for quoting the arguments
    depth = depth + num_parameters;

    // Quote each argument.
    let mut arguments = Vec::new();
    for (sem_arg, syn_ty) in sem_data.iter().zip(data_info.arguments.bindings) {
        // Evaluate the type of the current argument.
        let sem_ty = eval::eval(&mut env, &syn_ty).map_err(Error::EvalError)?;

        // Quote the current argument
        let syn_arg = quote(db, global, depth, &sem_ty, &sem_arg)?;
        arguments.push(syn_arg);

        // Push the semantic argument into the environment for subsequent iterations.
        env.push(sem_arg.clone());
    }
    Ok(Syntax::data_constructor_rc(constructor, arguments))
}

/// Read a variable back to syntax.
fn quote_variable<'db>(
    _db: &'db dyn salsa::Database,
    depth: usize,
    sem_var: &val::Variable,
) -> Result<'db, RcSyntax<'db>> {
    // Convert the DB level to an index, and return the syntactic variable.
    let syn_var = Syntax::variable(sem_var.level.to_index(depth));
    Ok(Rc::new(syn_var))
}

/// Read a metavariable back to syntax.
fn quote_metavariable<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    sem_meta: &val::MetaVariable<'db>,
) -> Result<'db, RcSyntax<'db>> {
    // Look up the metavariable info to get the argument types.
    let meta_info = global
        .metavariable(sem_meta.id)
        .map_err(|_| Error::IllTyped)?;

    // Create an environment for evaluating the type of each argument.
    let mut env = Environment {
        global: global,
        local: LocalEnv::new(),
    };

    // Quote each value in the local environment to build the substitution.
    let mut substitution = Vec::new();
    for (value, syn_ty) in sem_meta.local.iter().zip(meta_info.arguments.iter()) {
        // Evaluate the type of the current argument.
        let sem_ty = eval::eval(&mut env, &syn_ty).map_err(Error::EvalError)?;

        // Quote the current argument with its proper type.
        let quoted = quote(db, global, depth, &sem_ty, value)?;
        substitution.push(quoted);

        // Push the semantic argument into the environment for subsequent iterations.
        env.push(value.clone());
    }

    // Create the metavariable syntax node with the substitution.
    let meta_syntax = Syntax::metavariable(sem_meta.id, substitution);

    Ok(Rc::new(meta_syntax))
}

/// Read a stuck case expression back to syntax.
/// The scrutinee is already quoted and passed as `syn_scrutinee`.
fn quote_case_eliminator<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    syn_scrutinee: RcSyntax<'db>,
    sem_case: &val::Case<'db>,
) -> Result<'db, RcSyntax<'db>> {
    let type_info = global.type_constructor(sem_case.type_constructor)?;
    let num_parameters = type_info.num_parameters();

    let parameters = &sem_case.parameters;
    let index_bindings = type_info.arguments.bindings[num_parameters..].to_vec();
    let index_telescope = crate::syn::Telescope::from(index_bindings);
    let index_tys = eval_telescope(global, parameters.clone(), &index_telescope)?;

    let mut branches = Vec::new();
    for branch in &sem_case.branches {
        let data_info = global.data_constructor(branch.constructor)?;

        // Create an instance of this data constructor.
        let dcon_arg_tys = eval_telescope(global, parameters.clone(), &data_info.arguments)?;
        let mut dcon_args = Vec::new();
        for ty in dcon_arg_tys.types {
            dcon_args.push(Rc::new(Value::variable(
                Level::new(depth + dcon_args.len()),
                ty,
            )));
        }
        let mut dcon_env = LocalEnv::new();
        dcon_env.extend(parameters.clone());
        let dcon_ty_clos = Closure::new(dcon_env, data_info.ty.clone());
        let dcon_ty = eval::run_closure(global, &dcon_ty_clos, dcon_args.clone())?;
        let Value::TypeConstructor(tcon) = &*dcon_ty else {
            return Err(Error::IllTyped);
        };
        let dcon_val = Rc::new(Value::data_constructor(
            branch.constructor,
            dcon_args.clone(),
        ));
        // Create the arguments to the motive, by pulling the indices from the type constructor, and appending the data constructor.
        let mut motive_args = tcon.arguments[type_info.num_parameters..].to_vec();
        motive_args.push(dcon_val);
        let branch_ty = eval::run_closure(global, &sem_case.motive, motive_args)?;
        // Evaluate the branch body closure with the data constructor arguments
        let branch_val = eval::run_closure(global, &branch.body, dcon_args)?;
        let branch_syn = quote(db, global, depth + branch.arity, &*branch_ty, &*branch_val)?;
        branches.push(CaseBranch::new(
            branch.constructor,
            branch.arity,
            branch_syn,
        ));
    }

    // Read back the motive by creating a variable for the scrutinee.
    // Reconstruct the scrutinee type from the type constructor and parameters.
    let mut motive_args = Vec::new();
    for ty in index_tys.types {
        motive_args.push(Rc::new(Value::variable(
            Level::new(depth + motive_args.len()),
            ty,
        )));
    }
    let scrutinee_ty = Rc::new(Value::type_constructor(
        sem_case.type_constructor,
        sem_case.parameters.clone(),
    ));
    let scrutinee_var = Rc::new(Value::variable(Level::new(depth), scrutinee_ty));
    motive_args.push(scrutinee_var);
    let motive_args_len = motive_args.len();
    let sem_motive_result = eval::run_closure(global, &sem_case.motive, motive_args)?;
    let syn_motive = quote_type(db, global, depth + 1 + motive_args_len, &sem_motive_result)?;
    Ok(Syntax::case_rc(syn_scrutinee, syn_motive, branches))
}
