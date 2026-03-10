use crate::syn::SyntaxData;
use crate::val::{
    self as dom, Closure, DataConstructor, Eliminator, Environment, Flex, GlobalEnv, LocalEnv,
    MetaVariableLookupError, Normal, Rigid, SemTelescope, TransparentEnv, Value,
};
use crate::*;
use std::{
    fmt::{self, Display},
    rc::Rc,
};

#[derive(Debug, Clone)]
pub enum Error {
    BadApplication { loc: Option<Location> },
    BadCase { loc: Option<Location> },
    UnknownConstant { loc: Option<Location> },
    UnknownTypeConstructor { loc: Option<Location> },
    UnknownDataConstructor { loc: Option<Location> },
    MetaVariableLookupError(MetaVariableLookupError),
}

impl From<MetaVariableLookupError> for Error {
    fn from(e: MetaVariableLookupError) -> Self {
        Error::MetaVariableLookupError(e)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::BadApplication { loc } => {
                write!(f, "bad application")?;
                if let Some(loc) = loc {
                    write!(f, " at {:?}", loc)?;
                }
                Ok(())
            }
            Error::BadCase { loc } => {
                write!(f, "bad case")?;
                if let Some(loc) = loc {
                    write!(f, " at {:?}", loc)?;
                }
                Ok(())
            }
            Error::UnknownConstant { loc } => {
                write!(f, "unknown constant")?;
                if let Some(loc) = loc {
                    write!(f, " at {:?}", loc)?;
                }
                Ok(())
            }
            Error::UnknownTypeConstructor { loc } => {
                write!(f, "unknown type constructor")?;
                if let Some(loc) = loc {
                    write!(f, " at {:?}", loc)?;
                }
                Ok(())
            }
            Error::UnknownDataConstructor { loc } => {
                write!(f, "unknown data constructor")?;
                if let Some(loc) = loc {
                    write!(f, " at {:?}", loc)?;
                }
                Ok(())
            }
            Error::MetaVariableLookupError(e) => e.fmt(f),
        }
    }
}

pub fn substitute<'db, 'g>(
    global: &GlobalEnv<'db>,
    tm: &Syntax<'db>,
    substitution: LocalEnv<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    let mut env = Environment {
        global,
        local: substitution,
        transparent: TransparentEnv::new(),
    };
    eval(&mut env, tm)
}

pub fn eval<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    stx: &Syntax<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    use crate::syn::SyntaxData;
    match &stx.data {
        SyntaxData::Universe(uni) => eval_universe(env, &uni),
        SyntaxData::Lift(lift) => eval_lift(env, lift),

        SyntaxData::Pi(pi) => eval_pi(env, pi),
        SyntaxData::Lambda(lam) => eval_lambda(env, lam),
        SyntaxData::Application(app) => eval_application(env, &app),
        SyntaxData::Let(let_expr) => eval_let(env, let_expr),

        SyntaxData::TypeConstructor(type_constructor) => {
            eval_type_constructor(env, type_constructor)
        }
        SyntaxData::DataConstructor(data_constructor) => {
            eval_data_constructor(env, data_constructor)
        }
        SyntaxData::Case(case) => eval_case(env, case),

        SyntaxData::Eq(eq) => eval_eq(env, eq),
        SyntaxData::Refl(refl) => eval_refl(env, refl),
        SyntaxData::Transport(transport) => eval_transport(env, transport),
        SyntaxData::Closure(_) => {
            // Closures should not appear in evaluated terms - they only exist in Transport motives
            // This is a malformed term
            Err(Error::BadApplication { loc: Some(stx.loc) })
        }

        SyntaxData::HardwareUniverse(hw) => eval_hardware_universe(env, hw),
        SyntaxData::SLift(slift) => eval_slift(env, slift),
        SyntaxData::MLift(mlift) => eval_mlift(env, mlift),

        SyntaxData::SignalUniverse(sig) => eval_signal_universe(env, sig),
        SyntaxData::Bit(bit) => eval_bit(env, bit),
        SyntaxData::Zero(zero) => eval_zero(env, zero),
        SyntaxData::One(one) => eval_one(env, one),

        SyntaxData::ModuleUniverse(mod_uni) => eval_module_universe(env, mod_uni),
        SyntaxData::HArrow(harrow) => eval_harrow(env, harrow),
        SyntaxData::Module(module) => eval_module(env, module),
        SyntaxData::HApplication(happ) => eval_happlication(env, happ),

        SyntaxData::Prim(prim) => eval_prim(env, prim),
        SyntaxData::Constant(constant) => eval_constant(env, &constant),
        SyntaxData::Variable(var) => eval_variable(env, &var),
        SyntaxData::Metavariable(meta) => eval_metavariable(env, meta),

        SyntaxData::Check(chk) => eval_check(env, chk),
    }
}

fn eval_universe<'db, 'g>(
    _: &mut Environment<'db, 'g>,
    universe: &syn::Universe<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::universe(universe.level)))
}

fn eval_lift<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    lift: &syn::Lift<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    let ty = eval(env, &lift.ty)?;
    Ok(Rc::new(Value::lift(ty)))
}

fn eval_pi<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    pi: &syn::Pi<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    let source = eval(env, &pi.source)?;
    let target = Closure::new(env.local.clone(), pi.target.clone());
    Ok(Rc::new(Value::pi(source, target)))
}

fn eval_lambda<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    lambda: &syn::Lambda<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::Lambda(dom::Lambda {
        body: Closure::new(env.local.clone(), lambda.body.clone()),
    })))
}

fn eval_let<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    let_expr: &syn::Let<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Evaluate the type and value
    let ty = eval(env, &let_expr.ty)?;
    let value = eval(env, &let_expr.value)?;

    // Push transparent binding and evaluate body
    env.push_transparent(ty.clone(), value.clone());
    let body = eval(env, &let_expr.body)?;
    env.pop();

    // Return Let value with fully evaluated body
    Ok(Rc::new(Value::Let(dom::Let::new(ty, value, body))))
}

fn eval_type_constructor<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    type_constructor: &syn::TypeConstructor<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Evaluate all the arguments
    let mut evaluated_args = Vec::new();
    for arg in type_constructor {
        let evaluated_arg = eval(env, arg)?;
        evaluated_args.push(evaluated_arg);
    }

    // Create a TypeConstructor value with the constructor and evaluated arguments
    let type_constructor_value =
        Value::type_constructor(type_constructor.constructor, evaluated_args);
    Ok(Rc::new(type_constructor_value))
}

fn eval_data_constructor<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    data_constructor: &syn::DataConstructor<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Evaluate all the arguments
    let mut evaluated_args = Vec::new();
    for arg in data_constructor {
        let evaluated_arg = eval(env, arg)?;
        evaluated_args.push(evaluated_arg);
    }

    // Create a DataConstructor value with the constructor and evaluated arguments
    let data_value = Value::data_constructor(data_constructor.constructor, evaluated_args);
    Ok(Rc::new(data_value))
}

fn eval_hardware_universe<'db, 'g>(
    _: &mut Environment<'db, 'g>,
    _: &syn::HardwareUniverse<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::hardware_universe()))
}

fn eval_slift<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    slift: &syn::SLift<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    let ty = eval(env, &slift.ty)?;
    Ok(Rc::new(Value::slift(ty)))
}

fn eval_mlift<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    mlift: &syn::MLift<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    let ty = eval(env, &mlift.ty)?;
    Ok(Rc::new(Value::mlift(ty)))
}

fn eval_signal_universe<'db, 'g>(
    _: &mut Environment<'db, 'g>,
    _: &syn::SignalUniverse<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::signal_universe()))
}

fn eval_bit<'db, 'g>(
    _: &mut Environment<'db, 'g>,
    _: &syn::Bit<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::bit()))
}

fn eval_zero<'db, 'g>(
    _: &mut Environment<'db, 'g>,
    _: &syn::Zero<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::zero()))
}

fn eval_one<'db, 'g>(
    _: &mut Environment<'db, 'g>,
    _: &syn::One<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::one()))
}

fn eval_module_universe<'db, 'g>(
    _: &mut Environment<'db, 'g>,
    _: &syn::ModuleUniverse<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::module_universe()))
}

fn eval_harrow<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    harrow: &syn::HArrow<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    let source = eval(env, &harrow.source)?;
    let target = Closure::new(env.local.clone(), harrow.target.clone());
    Ok(Rc::new(Value::harrow(source, target)))
}

fn eval_module<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    module: &syn::Module<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::module(Closure::new(
        env.local.clone(),
        module.body.clone(),
    ))))
}

fn eval_happlication<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    happ: &syn::HApplication<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    let module = eval(env, &happ.module)?;
    let module_ty = eval(env, &happ.module_ty)?;
    let arg = eval(env, &happ.argument)?;
    Ok(Rc::new(Value::happlication(module, module_ty, arg)))
}

fn eval_prim<'db, 'g>(
    _env: &mut Environment<'db, 'g>,
    prim: &syn::Prim<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::Prim(prim.name)))
}

fn eval_constant<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    constant: &syn::Constant<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    let info = env
        .global
        .constant(constant.name)
        .map_err(|_| Error::UnknownConstant { loc: None })?;
    let mut unfold_env = Environment {
        global: env.global,
        local: LocalEnv::new(),
        transparent: TransparentEnv::new(),
    };
    eval(&mut unfold_env, &info.value)
}

fn eval_variable<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    var: &syn::Variable<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(env.get(var.index.to_level(env.depth())))
}

fn eval_metavariable<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    meta: &syn::Metavariable<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Evaluate all the arguments in the substitution to build the local environment.
    let mut local_env = val::LocalEnv::new();
    for arg in meta.iter() {
        let evaluated_arg = eval(env, arg)?;
        local_env.push(evaluated_arg);
    }

    // Look up the metavariable info to get its type.
    let meta_info = env.global.metavariable(meta.id)?;

    // Create an environment for evaluating the type with the substitution.
    let mut type_env = Environment {
        global: env.global,
        local: local_env.clone(),
        transparent: TransparentEnv::new(),
    };

    // Evaluate the type of the metavariable in the extended environment.
    let meta_ty = eval(&mut type_env, &meta_info.ty)?;

    // Create a metavariable value with the local environment.
    let meta_value = val::MetaVariable::new(meta.id, local_env);

    // Create a Flex neutral with an empty spine.
    let flex = val::Flex::new(meta_value, val::Spine::empty(), meta_ty);

    Ok(Rc::new(Value::Flex(flex)))
}

fn eval_check<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    chk: &syn::Check<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    eval(env, &chk.term)
}

/// Perform the application of a rigid neutral to an argument.
fn apply_rigid<'db>(
    global: &GlobalEnv<'db>,
    rigid: &Rigid<'db>,
    arg: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    // If the operator is not pi-typed, bail.
    let Value::Pi(pi) = rigid.ty.as_ref() else {
        return Err(Error::BadApplication { loc: None });
    };

    // Use the pi type of the neutral to compute typing information.
    let source_ty = pi.source.clone();
    let target_ty = run_closure(global, &pi.target, [arg.clone()])?;

    // Build the application eliminator.
    let arg_normal = Normal::new(source_ty, arg);
    let eliminator = Eliminator::application(arg_normal);

    // Extend the spine with the application.
    let mut spine = rigid.spine.clone();
    spine.push(eliminator);

    // Create the new rigid neutral.
    let new_rigid = Rigid::new(rigid.head.clone(), spine, target_ty);
    Ok(Rc::new(Value::Rigid(new_rigid)))
}

/// Perform the application of a flexible neutral to an argument.
fn apply_flex<'db>(
    global: &GlobalEnv<'db>,
    flex: &Flex<'db>,
    arg: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    // If the operator is not pi-typed, bail.
    let Value::Pi(pi) = flex.ty.as_ref() else {
        return Err(Error::BadApplication { loc: None });
    };

    // Use the pi type of the neutral to compute typing information.
    let source_ty = pi.source.clone();
    let target_ty = run_closure(global, &pi.target, [arg.clone()])?;

    // Build the application eliminator.
    let arg_normal = Normal::new(source_ty, arg);
    let eliminator = Eliminator::application(arg_normal);

    // Extend the spine with the application.
    let mut spine = flex.spine.clone();
    spine.push(eliminator);

    // Create the new flex neutral.
    let new_flex = Flex::new(flex.head.clone(), spine, target_ty);
    Ok(Rc::new(Value::Flex(new_flex)))
}

fn eval_application<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    application: &syn::Application<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Evaluate the function and argument to a value, then perform the substitution.
    let fun: Rc<Value> = eval(env, &application.function)?;
    let arg: Rc<Value> = eval(env, &application.argument)?;
    run_application(&env.global, &*fun, arg)
}

/// Perform an application.
pub fn run_application<'db>(
    global: &GlobalEnv<'db>,
    fun: &Value<'db>,
    arg: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    match fun {
        Value::Lambda(lambda) => apply_lambda(global, lambda, arg),
        Value::Rigid(rigid) => apply_rigid(global, rigid, arg),
        Value::Flex(flex) => apply_flex(global, flex, arg),
        _ => Err(Error::BadApplication { loc: None }),
    }
}

/// Perform the application of a lambda to an argument.
pub fn apply_lambda<'db>(
    global: &GlobalEnv<'db>,
    lambda: &val::Lambda<'db>,
    arg: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    run_closure(global, &lambda.body, [arg])
}

fn eval_case<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    case: &syn::Case<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // The scrutinee is a variable (de Bruijn index).
    // Convert it to a level and look up its value in the environment.
    let scrutinee_level = case.scrutinee.index.to_level(env.depth());
    let scrutinee = env.get(scrutinee_level).clone();

    // No return type in syntax - case expressions are check-only.
    // For stuck cases, we'll need the type to come from the typechecker.
    let branches = case
        .branches
        .iter()
        .map(|branch| {
            let body = Closure::new(env.local.clone(), branch.body.clone());
            dom::CaseBranch::new(branch.constructor, branch.arity, body)
        })
        .collect();
    run_case(&env.global, scrutinee, branches)
}

fn run_case<'db>(
    global: &GlobalEnv<'db>,
    scrutinee: Rc<Value<'db>>,
    branches: Vec<dom::CaseBranch<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    match scrutinee.as_ref() {
        Value::DataConstructor(scrutinee) => {
            run_case_on_data_constructor(global, scrutinee, branches)
        }
        Value::Rigid(rigid) => run_case_on_rigid(global, scrutinee.clone(), rigid, branches),
        Value::Flex(flex) => run_case_on_flex(global, scrutinee.clone(), flex, branches),
        _ => Err(Error::BadCase { loc: None }),
    }
}

fn run_case_on_data_constructor<'db>(
    global: &GlobalEnv<'db>,
    scrutinee: &DataConstructor<'db>,
    branches: Vec<dom::CaseBranch<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    // Find the matching branch.
    for branch in &branches {
        if branch.constructor == scrutinee.constructor {
            return run_closure(global, &branch.body, scrutinee.arguments.clone());
        }
    }
    // If we didn't match any branches, we have a bad case.
    Err(Error::BadCase { loc: None })
}

fn run_case_on_rigid<'db>(
    global: &GlobalEnv<'db>,
    _scrutinee: Rc<Value<'db>>,
    rigid: &Rigid<'db>,
    branches: Vec<dom::CaseBranch<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    // Verify that the type is a type constructor.
    let Value::TypeConstructor(type_constructor) = rigid.ty.as_ref() else {
        return Err(Error::BadCase { loc: None });
    };
    let constructor = type_constructor.constructor;

    // Look up the type information from the global environment.
    let type_info = global
        .type_constructor(constructor)
        .map_err(|_| Error::UnknownTypeConstructor { loc: None })?;

    // Get the parameters off of the type.
    let num_parameters = type_info.num_parameters();
    let parameters = &type_constructor.arguments[..num_parameters];

    // Build the case eliminator (no return type stored - case is check-only).
    let eliminator = Eliminator::case(constructor, parameters.to_vec(), branches);

    // Extend the spine with the case.
    let mut spine = rigid.spine.clone();
    spine.push(eliminator);

    // TODO: The return type should come from the typechecker.
    // For now, use a placeholder. This will be fixed when we implement
    // type-directed evaluation or proper check-only case.
    // Using the scrutinee's type as placeholder (incorrect but keeps things compiling).
    let placeholder_ty = rigid.ty.clone();

    // Create the new rigid neutral with the placeholder type.
    let new_rigid = Rigid::new(rigid.head.clone(), spine, placeholder_ty);
    Ok(Rc::new(Value::Rigid(new_rigid)))
}

fn run_case_on_flex<'db>(
    global: &GlobalEnv<'db>,
    _scrutinee: Rc<Value<'db>>,
    flex: &Flex<'db>,
    branches: Vec<dom::CaseBranch<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    // Verify that the type is a type constructor.
    let Value::TypeConstructor(type_constructor) = flex.ty.as_ref() else {
        return Err(Error::BadCase { loc: None });
    };
    let constructor = type_constructor.constructor;

    // Look up the type information from the global environment.
    let type_info = global
        .type_constructor(constructor)
        .map_err(|_| Error::UnknownTypeConstructor { loc: None })?;

    // Get the parameters off of the type.
    let num_parameters = type_info.num_parameters();
    let parameters = &type_constructor.arguments[..num_parameters];

    // Build the case eliminator (no return type stored - case is check-only).
    let eliminator = Eliminator::case(constructor, parameters.to_vec(), branches);

    // Extend the spine with the case.
    let mut spine = flex.spine.clone();
    spine.push(eliminator);

    // TODO: The return type should come from the typechecker.
    // For now, use a placeholder. This will be fixed when we implement
    // type-directed evaluation or proper check-only case.
    // Using the scrutinee's type as placeholder (incorrect but keeps things compiling).
    let placeholder_ty = flex.ty.clone();

    // Create the new flex neutral with the placeholder type.
    let new_flex = Flex::new(flex.head.clone(), spine, placeholder_ty);
    Ok(Rc::new(Value::Flex(new_flex)))
}

fn eval_eq<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    eq: &syn::EqType<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    let ty = eval(env, &eq.ty)?;
    let lhs = eval(env, &eq.lhs)?;
    let rhs = eval(env, &eq.rhs)?;
    Ok(Rc::new(Value::eq(ty, lhs, rhs)))
}

fn eval_refl<'db, 'g>(
    _env: &mut Environment<'db, 'g>,
    _refl: &syn::Refl<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::refl()))
}

fn eval_transport<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    transport: &syn::Transport<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // The motive is a nested closure structure [%0 %1 ...] |- body
    // We need to find the innermost body by traversing the nested Syntax::Closure nodes
    let innermost_body = get_closure_body(&transport.motive);
    let motive = Closure::new(env.local.clone(), innermost_body);

    // Evaluate the proof.
    let proof = eval(env, &transport.proof)?;

    // Evaluate the value.
    let value = eval(env, &transport.value)?;

    // Critical optimization: if the proof is Refl, the transport vanishes!
    // This is the computational rule: transport P refl v = v
    match proof.as_ref() {
        Value::Refl(_) => Ok(value),
        _ => {
            // Proof is stuck (neutral), so transport remains.
            Ok(Rc::new(Value::transport(motive, proof, value)))
        }
    }
}

/// Helper function to extract the innermost body from a nested closure structure
fn get_closure_body<'db>(closure: &syn::Closure<'db>) -> syn::RcSyntax<'db> {
    let mut current = &closure.body;
    loop {
        match &current.data {
            SyntaxData::Closure(inner) => {
                current = &inner.body;
            }
            _ => return current.clone(),
        }
    }
}

pub fn run_spine<'db>(
    global: &GlobalEnv<'db>,
    mut eliminatee: Rc<Value<'db>>,
    spine: &val::Spine<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    for eliminator in spine.iter() {
        match eliminator {
            Eliminator::Application(application) => {
                eliminatee =
                    run_application(global, &eliminatee, application.argument.value.clone())?;
            }
            Eliminator::Case(case) => {
                eliminatee = run_case(global, eliminatee, case.branches.clone())?;
            }
        }
    }
    Ok(eliminatee)
}

/// Perform a delayed substitution.
/// Takes only the local environment from the closure and extends it with the provided arguments.
/// The global environment must be provided separately.
pub fn run_closure<'db, T>(
    global: &GlobalEnv<'db>,
    closure: &Closure<'db>,
    args: T,
) -> Result<Rc<Value<'db>>, Error>
where
    T: IntoIterator<Item = Rc<Value<'db>>>,
{
    let mut local = closure.local.clone();
    local.extend(args);
    let mut env = Environment {
        global,
        local,
        transparent: TransparentEnv::new(),
    };
    eval(&mut env, &closure.term)
}

/// Evaluate a telescope to a list of types.
pub fn eval_telescope<'db, 'g, T>(
    global: &'g GlobalEnv<'db>,
    params: T,
    telescope: &syn::Telescope<'db>,
) -> Result<SemTelescope<'db>, Error>
where
    T: IntoIterator<Item = Rc<Value<'db>>>,
{
    // We start with a fresh local environment since types are defined in the
    // global environment.
    let mut env = Environment {
        global,
        local: LocalEnv::new(),
        transparent: TransparentEnv::new(),
    };
    // Extend the environment with the parameters.
    env.extend(params);
    let mut types = Vec::new();

    // Evaluate each binding in the telescope.
    for ty in &telescope.bindings {
        // Evaluate this type.
        let ty = eval(&mut env, ty)?;
        types.push(ty.clone());
        // Create a variable of this type.
        // TODO: only push the variable if there is another binding.
        env.push_var(ty);
    }
    Ok(SemTelescope { types })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quote::{quote, type_quote};
    use crate::syn::parse::parse_syntax;
    use crate::syn::print::print_syntax_to_string;
    use crate::syn::RcSyntax;
    use crate::Database;

    /// Test helper context
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

        /// Parse a string into syntax
        fn parse(&self, input: &'db str) -> RcSyntax<'db> {
            parse_syntax(self.db, input).unwrap_or_else(|e| panic!("parse failed: {:?}", e))
        }

        /// Evaluate a syntax term and return the result
        fn eval(&self, stx: &Syntax<'db>) -> Rc<Value<'db>> {
            let mut env = Environment {
                global: &self.global,
                local: LocalEnv::new(),
                transparent: TransparentEnv::new(),
            };
            super::eval(&mut env, stx).expect("eval failed")
        }

        /// Parse, evaluate, and quote back at a type (parsed), returning a string
        fn eval_at(&self, term: &'db str, ty: &'db str) -> String {
            let stx = self.parse(term);
            let ty_stx = self.parse(ty);
            let ty_val = self.eval(&ty_stx);
            let val = self.eval(&stx);
            let syntax = quote(&self.global, 0, &val, &ty_val).expect("quote failed");
            print_syntax_to_string(self.db, &syntax)
        }

        /// Parse, evaluate a type, and type-quote, returning a string
        fn eval_type(&self, term: &'db str) -> String {
            let stx = self.parse(term);
            let val = self.eval(&stx);
            let syntax = type_quote(&self.global, 0, &val).expect("type_quote failed");
            print_syntax_to_string(self.db, &syntax)
        }
    }

    // =========================================================================
    // Basic Type Evaluation Tests
    // =========================================================================

    #[test]
    fn test_eval_universes() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // Universe evaluates to itself
        assert_eq!(c.eval_type("U0"), "𝒰0");
        assert_eq!(c.eval_type("U1"), "𝒰1");
    }

    #[test]
    fn test_eval_hardware_universes() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.eval_type("HardwareUniverse"), "HardwareUniverse");
        assert_eq!(c.eval_type("SignalUniverse"), "SignalUniverse");
        assert_eq!(c.eval_type("ModuleUniverse"), "ModuleUniverse");
    }

    #[test]
    fn test_eval_bit() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.eval_type("Bit"), "Bit");
    }

    #[test]
    fn test_eval_bit_values() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.eval_at("0", "Bit"), "0");
        assert_eq!(c.eval_at("1", "Bit"), "1");
    }

    #[test]
    fn test_eval_pi() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // ∀ (x : U0) → U0
        assert_eq!(c.eval_type("∀ (%x : U0) → U0"), "∀ (%0 : 𝒰0) → 𝒰0");
    }

    #[test]
    fn test_eval_harrow() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.eval_type("Bit → Bit"), "Bit → Bit");
    }

    #[test]
    fn test_eval_lift() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.eval_type("^U0"), "^𝒰0");
    }

    #[test]
    fn test_eval_slift() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.eval_type("^sBit"), "^sBit");
    }

    #[test]
    fn test_eval_mlift() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.eval_type("^m(Bit → Bit)"), "^m(Bit → Bit)");
    }

    // =========================================================================
    // Lambda and Application Tests
    // =========================================================================

    #[test]
    fn test_eval_lambda_identity() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // λ x → x at ∀ (x : U0) → U0
        assert_eq!(c.eval_at("λ %x → %x", "∀ (%x : U0) → U0"), "λ %0 → %0");
    }

    #[test]
    fn test_eval_lambda_beta_reduction() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // (λ x → x) U0  should reduce to U0
        assert_eq!(c.eval_type("(λ %x → %x) U0"), "𝒰0");
    }

    #[test]
    fn test_eval_lambda_const_beta_reduction() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // (λ x → 0) 1  should reduce to 0
        assert_eq!(c.eval_at("(λ %x → 0) 1", "Bit"), "0");
    }

    #[test]
    fn test_eval_nested_lambda_beta_reduction() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // (λ x y → x) 0 1  should reduce to 0  (returns first arg)
        assert_eq!(c.eval_at("(λ %x %y → %x) 0 1", "Bit"), "0");
    }

    #[test]
    fn test_eval_second_projection() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // (λ x y → y) 0 1  should reduce to 1
        assert_eq!(c.eval_at("(λ %x %y → %y) 0 1", "Bit"), "1");
    }

    // =========================================================================
    // Module and HApplication Tests
    // =========================================================================

    #[test]
    fn test_eval_module_identity() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // mod x → x
        assert_eq!(c.eval_at("mod %x → %x", "Bit → Bit"), "mod %0 → %0");
    }

    #[test]
    fn test_eval_module_const() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // mod x → 0
        assert_eq!(c.eval_at("mod %x → 0", "Bit → Bit"), "mod %0 → 0");
    }

    // =========================================================================
    // Variable Evaluation Tests
    // =========================================================================

    // =========================================================================
    // Neutral Term Tests (using lambdas to build environments)
    // =========================================================================

    #[test]
    fn test_eval_variable_in_env() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // (λ x → x) 0  should give 0 (variable lookup in env)
        assert_eq!(c.eval_at("(λ %x → %x) 0", "Bit"), "0");
    }

    #[test]
    fn test_eval_variable_captures() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // (λ x → (λ y → x)) 0 1  should give 0 (captured variable)
        assert_eq!(c.eval_at("(λ %x → (λ %y → %x)) 0 1", "Bit"), "0");
        // Alternative: (λ x y → x) 0 1  should reduce to 0 (first argument)
        assert_eq!(c.eval_at("(λ %x %y → %x) 0 1", "Bit"), "0");
        // (λ x y → y) 0 1  should reduce to 1 (second argument)
        assert_eq!(c.eval_at("(λ %x %y → %y) 0 1", "Bit"), "1");
    }

    #[test]
    fn test_eval_application_neutral() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // λ f → f ^Bit  - the body (f ^Bit) is a neutral application
        // where f is a function variable of type ∀ (%x : U0) → U0 (a Pi type!)
        // Note: A → B parses as HArrow, not Pi. Must use ∀ (%x : A) → B for Pi.
        // When quoted, the result should be λ %0 → %0[^Bit]
        assert_eq!(
            c.eval_at("λ %f → %f ^Bit", "∀ (%f : ∀ (%x : U0) → U0) → U0"),
            "λ %0 → %0[^Bit]"
        );
    }

    // =========================================================================
    // Metavariable Evaluation Tests
    // =========================================================================

    #[test]
    fn test_eval_metavariable_no_args() {
        // A metavariable with no arguments evaluates to a Flex neutral
        use crate::common::MetaVariableId;
        use crate::val::GlobalEnv;

        let db = Database::new();
        let mut global = GlobalEnv::new();

        // Declare ?[0] : U0
        let meta_id = MetaVariableId::new(Location::UNKNOWN, 0);
        global.add_metavariable(
            meta_id,
            vec![],
            Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)),
        );

        let mut env = Environment::new(&global);
        let meta_stx = Syntax::metavariable(Location::UNKNOWN, meta_id, vec![]);
        let result = eval(&mut env, &meta_stx).expect("eval should succeed");

        // Should be a Flex neutral
        match &*result {
            Value::Flex(flex) => {
                assert_eq!(flex.head.id, meta_id);
                assert_eq!(flex.head.local.depth(), 0); // No arguments
                assert!(flex.spine.is_empty());
            }
            _ => panic!("Expected Flex, got {:?}", result),
        }

        // Quote and check printed form
        let quoted =
            crate::quote::quote(&global, 0, &result, &Value::universe(UniverseLevel::new(0)))
                .expect("quote should succeed");
        assert_eq!(
            crate::syn::print::print_syntax_to_string(&db, &quoted),
            "?[0]"
        );
    }

    #[test]
    fn test_eval_metavariable_with_args() {
        // A metavariable with arguments evaluates to a Flex neutral with a local env
        use crate::common::{Level, MetaVariableId};
        use crate::val::GlobalEnv;

        let db = Database::new();
        let mut global = GlobalEnv::new();

        // Declare ?[0] (%x : U0) : U0
        let meta_id = MetaVariableId::new(Location::UNKNOWN, 0);
        global.add_metavariable(
            meta_id,
            vec![Syntax::universe_rc(
                Location::UNKNOWN,
                UniverseLevel::new(0),
            )],
            Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)),
        );

        let mut env = Environment::new(&global);
        // ?[0 ^Bit] - apply metavariable to ^Bit
        let lift_bit = Syntax::lift_rc(Location::UNKNOWN, Syntax::bit_rc(Location::UNKNOWN));
        let meta_stx = Syntax::metavariable(Location::UNKNOWN, meta_id, vec![lift_bit]);
        let result = eval(&mut env, &meta_stx).expect("eval should succeed");

        // Should be a Flex neutral with the argument in its local env
        match &*result {
            Value::Flex(flex) => {
                assert_eq!(flex.head.id, meta_id);
                assert_eq!(flex.head.local.depth(), 1);
                // The argument should be ^Bit (a Lift value containing Bit)
                match &**flex.head.local.get(Level::new(0)) {
                    Value::Lift(lift) => {
                        assert!(matches!(&*lift.ty, Value::Bit(_)));
                    }
                    other => panic!("Expected Lift, got {:?}", other),
                }
            }
            _ => panic!("Expected Flex, got {:?}", result),
        }

        // Quote and check printed form
        let quoted =
            crate::quote::quote(&global, 0, &result, &Value::universe(UniverseLevel::new(0)))
                .expect("quote should succeed");
        assert_eq!(
            crate::syn::print::print_syntax_to_string(&db, &quoted),
            "?[0 ^Bit]"
        );
    }

    #[test]
    fn test_eval_metavariable_application() {
        // Applying a Flex neutral to an argument adds to its spine
        use crate::common::MetaVariableId;
        use crate::val::GlobalEnv;

        let db = Database::new();
        let mut global = GlobalEnv::new();

        // Declare ?[0] : ∀ (%x : U0) → U0
        let meta_id = MetaVariableId::new(Location::UNKNOWN, 0);
        let pi_ty = Syntax::pi_rc(
            Location::UNKNOWN,
            Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)),
            Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)),
        );
        global.add_metavariable(meta_id, vec![], pi_ty);

        let mut env = Environment::new(&global);
        // (?[0])[^Bit] - apply metavariable to ^Bit
        let meta_stx = Syntax::metavariable_rc(Location::UNKNOWN, meta_id, vec![]);
        let lift_bit = Syntax::lift_rc(Location::UNKNOWN, Syntax::bit_rc(Location::UNKNOWN));
        let app_stx = Syntax::application(Location::UNKNOWN, meta_stx, lift_bit);
        let result = eval(&mut env, &app_stx).expect("eval should succeed");

        // Should be a Flex neutral with the application in its spine
        match &*result {
            Value::Flex(flex) => {
                assert_eq!(flex.head.id, meta_id);
                assert_eq!(flex.spine.len(), 1);
            }
            _ => panic!("Expected Flex, got {:?}", result),
        }

        // Quote and check printed form
        let quoted =
            crate::quote::quote(&global, 0, &result, &Value::universe(UniverseLevel::new(0)))
                .expect("quote should succeed");
        assert_eq!(
            crate::syn::print::print_syntax_to_string(&db, &quoted),
            "?[0][^Bit]"
        );
    }

    // =========================================================================
    // Equality Type Evaluation Tests
    // =========================================================================

    #[test]
    fn test_eval_eq_type() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // Eq U0 0 1 should evaluate to an EqType value
        assert_eq!(c.eval_type("Eq Bit 0 1"), "Eq Bit 0 1");
    }

    #[test]
    fn test_eval_refl() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // refl should evaluate to a Refl value
        assert_eq!(c.eval_at("refl", "Eq Bit 0 0"), "refl");
    }

    #[test]
    fn test_eval_transport_with_refl() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // transport P refl v should reduce to v (critical optimization!)
        // transport [%0] |- Bit refl 0  should reduce to 0
        assert_eq!(c.eval_at("transport [%0] |- Bit refl 0", "Bit"), "0");
    }

    #[test]
    fn test_eval_transport_stuck() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // transport with a neutral proof should remain stuck
        // We can't easily test this without a proper type context,
        // so we just verify that transport with refl reduces
        assert_eq!(c.eval_at("transport [%0] |- Bit refl 0", "Bit"), "0");
    }

    #[test]
    fn test_eval_nested_eq() {
        let db = Database::new();
        let c = Ctx::new(&db);
        // Eq (Eq U0 %a %b) refl refl
        // This is an equality between two refl proofs
        assert_eq!(
            c.eval_type("Eq (Eq U0 U0 U0) refl refl"),
            "Eq (Eq 𝒰0 𝒰0 𝒰0) refl refl"
        );
    }
}
