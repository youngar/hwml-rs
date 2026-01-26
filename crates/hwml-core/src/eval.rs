use crate::val::{
    self as dom, Closure, DataConstructor, Eliminator, Environment, Flex, GlobalEnv, HEnvironment,
    LocalEnv, MetaVariableLookupError, Normal, Rigid, SemTelescope, Value, Value,
};
use crate::*;
use std::{
    fmt::{self, Display},
    rc::Rc,
};

#[derive(Debug, Clone)]
pub enum Error {
    BadApplication,
    BadCase,
    UnknownConstant,
    UnknownTypeConstructor,
    UnknownDataConstructor,
    MetaVariableLookupError(MetaVariableLookupError),
    BadSplice,
}

impl From<MetaVariableLookupError> for Error {
    fn from(e: MetaVariableLookupError) -> Self {
        Error::MetaVariableLookupError(e)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::BadApplication => write!(f, "bad application"),
            Error::BadCase => write!(f, "bad case"),
            Error::UnknownConstant => write!(f, "unknown constant"),
            Error::UnknownTypeConstructor => write!(f, "unknown type constructor"),
            Error::UnknownDataConstructor => write!(f, "unknown data constructor"),
            Error::BadSplice => write!(f, "bad splice"),
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
    };
    eval(&mut env, tm)
}

pub fn eval<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    stx: &Syntax<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    match stx {
        Syntax::Constant(constant) => eval_constant(env, &constant),
        Syntax::Variable(var) => eval_variable(env, &var),
        Syntax::Check(chk) => eval_check(env, chk),
        Syntax::Pi(pi) => eval_pi(env, pi),
        Syntax::Lambda(lam) => eval_lambda(env, lam),
        Syntax::TypeConstructor(type_constructor) => eval_type_constructor(env, type_constructor),
        Syntax::DataConstructor(data_constructor) => eval_data_constructor(env, data_constructor),
        Syntax::Application(app) => eval_application(env, &app),
        Syntax::Case(case) => eval_case(env, case),
        Syntax::Universe(uni) => eval_universe(env, &uni),
        Syntax::Metavariable(meta) => eval_metavariable(env, meta),
        Syntax::Prim(prim) => eval_prim(env, prim),
        // HardwareUniverse constructs
        Syntax::Bit(_) => eval_bit(env),
        Syntax::HardwareUniverse(_) => eval_hw_universe(env),
        Syntax::HArrow(harrow) => eval_harrow(env, harrow),
        Syntax::Lift(lift) => eval_lift(env, lift),
        Syntax::Quote(quote) => eval_quote(env, quote),
        Syntax::SignalUniverse(_) | Syntax::ModuleUniverse(_) => {
            todo!("evaluation of SignalUniverse and ModuleUniverse is not implemented yet")
        }
    }
}

/// Evaluate a constant by eagerly unfolding its definition.
/// Meta-level constants are always unfolded to their values.
fn eval_constant<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    constant: &syn::Constant<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Look up the constant's definition
    let info = env
        .global
        .constant(constant.name)
        .map_err(|_| Error::UnknownConstant)?;

    // Evaluate the constant's body in an empty local environment
    // (constants are top-level definitions with no free variables)
    let mut unfold_env = Environment {
        global: env.global,
        local: LocalEnv::new(),
    };
    eval(&mut unfold_env, &info.value)
}

fn eval_prim<'db, 'g>(
    _env: &mut Environment<'db, 'g>,
    prim: &syn::Prim<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::Prim(prim.name)))
}

fn eval_variable<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    var: &syn::Variable<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(env.get(var.index.to_level(env.depth())).clone())
}

fn eval_check<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    chk: &syn::Check<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    eval(env, &chk.term)
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

fn eval_universe<'db, 'g>(
    _: &mut Environment<'db, 'g>,
    universe: &syn::Universe<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::universe(universe.level)))
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
    };

    // Evaluate the type of the metavariable in the extended environment.
    let meta_ty = eval(&mut type_env, &meta_info.ty)?;

    // Create a metavariable value with the local environment.
    let meta_value = val::MetaVariable::new(meta.id, local_env);

    // Create a Flex neutral with an empty spine.
    let flex = val::Flex::new(meta_value, val::Spine::empty(), meta_ty);

    Ok(Rc::new(Value::Flex(flex)))
}

// ============================================================================
// HardwareUniverse Construct Evaluation
// ============================================================================

/// Evaluate the Bit type.
/// Bit : Type
fn eval_bit<'db, 'g>(_env: &mut Environment<'db, 'g>) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::bit()))
}

/// Evaluate the Type type.
/// Type : Type
fn eval_hw_universe<'db, 'g>(_env: &mut Environment<'db, 'g>) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::HardwareUniverse()))
}

/// Evaluate a hardware arrow type.
/// (a -> b) : Type when a, b : Type
fn eval_harrow<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    harrow: &syn::HArrow<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    let source = eval(env, &harrow.source)?;
    let target = eval(env, &harrow.target)?;
    Ok(Rc::new(Value::harrow(source, target)))
}

/// Evaluate a lifted hardware type.
/// ^ht : Type when ht : Type
fn eval_lift<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    lift: &syn::Lift<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    let hw_type = eval(env, &lift.tm)?;
    Ok(Rc::new(Value::lift(hw_type)))
}

/// Evaluate a quoted hardware term.
/// 'circuit : ^ht when circuit : HWTerm ht
fn eval_quote<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    quote: &syn::Quote<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Evaluate the hardware term to a hardware value
    let mut henv = HEnvironment::new();
    let hw_value = eval_hardware(&mut henv, env, &quote.tm)?;
    Ok(Rc::new(Value::quote(hw_value)))
}

/// Evaluate hardware term to hardware value.
/// This performs proper normalization including beta-reduction and primitive operations.
pub fn eval_hardware<'db, 'g>(
    henv: &mut HEnvironment<'db>,
    env: &mut Environment<'db, 'g>,
    hsyntax: &syn::HSyntax<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    match hsyntax {
        // Canonical bit values
        syn::HSyntax::Zero(_) => Ok(Rc::new(Value::Zero)),
        syn::HSyntax::One(_) => Ok(Rc::new(Value::One)),

        // HardwareUniverse variable - look up in hardware environment
        syn::HSyntax::HVariable(var) => {
            let level = var.index.to_level(henv.depth());
            henv.get(level).cloned().ok_or(Error::BadApplication)
        }

        // HardwareUniverse constant - treat as neutral
        syn::HSyntax::HConstant(hconst) => {
            // HardwareUniverse constants are references to user-defined hardware functions
            // They evaluate to neutral values (like variables)
            Ok(Rc::new(Value::HConstant(hconst.name)))
        }

        // Lambda: create a closure
        syn::HSyntax::Module(lam) => {
            // Capture both the current hardware environment and the current
            // meta-level local environment. This ensures that splices inside
            // the lambda body that reference meta-level variables (e.g. in
            // recursive generators) continue to see the correct environment
            // when the closure is later applied during evaluation/quotation.
            Ok(Rc::new(Value::Module(
                henv.clone(),
                env.local.clone(),
                lam.body.clone(),
            )))
        }

        // Application: evaluate and potentially beta-reduce
        syn::HSyntax::HApplication(app) => {
            let fun = eval_hardware(henv, env, &app.function)?;
            let arg = eval_hardware(henv, env, &app.argument)?;
            apply_hardware(henv, env, fun, arg)
        }

        // Splice: THE BRIDGE from meta to hardware
        syn::HSyntax::Splice(splice) => {
            let meta_val = eval(env, &splice.term)?;

            match &*meta_val {
                // Success: The meta-computation produced a Quote value
                Value::Quote(hw_value) => Ok(hw_value.clone()),

                // Stuck: The meta-computation hit a neutral (variable/metavar)
                // Embed it as a neutral in the hardware value
                Value::Rigid(_) | Value::Flex(_) => Ok(Rc::new(Value::splce(splice.term.clone()))),

                // Type error: splicing something that's not code or neutral
                _ => Err(Error::BadSplice),
            }
        }

        // Type check: just evaluate the term
        syn::HSyntax::HCheck(check) => eval_hardware(henv, env, &check.term),

        // HardwareUniverse primitive reference
        syn::HSyntax::HPrim(hprim) => Ok(Rc::new(Value::HPrim(hprim.name))),
    }
}

/// Apply a hardware function to an argument (during evaluation).
/// This is used internally when evaluating hardware applications.
fn apply_hardware<'db, 'g>(
    _henv: &mut HEnvironment<'db>,
    env: &mut Environment<'db, 'g>,
    fun: Rc<Value<'db>>,
    arg: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    match &*fun {
        // Beta-reduction: apply lambda
        Value::Module(closure) => run_hclosure(env.global, closure, [arg]),

        // Neutral application: create HApp
        Value::HVariable(_)
        | Value::Splice(_)
        | Value::HConstant(_)
        | Value::HPrim(_)
        | Value::HApp(_, _) => Ok(Rc::new(Value::happ(fun, arg))),

        // Type error: trying to apply non-function
        _ => Err(Error::BadApplication),
    }
}

/// Run a hardware closure with arguments.
/// This is analogous to `run_closure` for meta-level closures.
///
/// HardwareUniverse closures store syntax + an environment. To apply them, we:
/// 1. Clone the closure's hardware environment
/// 2. Extend it with the arguments
/// 3. Re-evaluate the body
///
pub fn run_hclosure<'db, T>(
    global: &GlobalEnv<'db>,
    closure: &dom::HClosure<'db>,
    args: T,
) -> Result<Rc<Value<'db>>, Error>
where
    T: IntoIterator<Item = Rc<Value<'db>>>,
{
    let mut henv = closure.env.clone();
    for arg in args {
        henv.push(arg);
    }
    let mut meta_env = Environment {
        global,
        // Reuse the captured meta-level local environment so that splices
        // inside the hardware closure body can correctly reference
        // meta-level variables that were in scope when the closure was
        // created (e.g. the `%m` in the `@Succ %m` branch of QueueGen).
        local: closure.local.clone(),
    };
    eval_hardware(&mut henv, &mut meta_env, &closure.body)
}

/// Apply a hardware value to an argument (in the value domain).
/// This is the hardware equivalent of `run_application`.
///
/// Used during quotation to apply hardware lambdas to fresh variables.
pub fn apply_Value<'db>(
    global: &GlobalEnv<'db>,
    fun: &Value<'db>,
    arg: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    match fun {
        // Beta-reduction: apply lambda via run_hclosure
        Value::Module(closure) => run_hclosure(global, closure, [arg]),

        // Neutral application: create HApp node
        Value::HVariable(_)
        | Value::Splice(_)
        | Value::HConstant(_)
        | Value::HPrim(_)
        | Value::HApp(_, _) => Ok(Rc::new(Value::happ(Rc::new(fun.clone()), arg))),

        // Type error: trying to apply non-function
        _ => Err(Error::BadApplication),
    }
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
        _ => Err(Error::BadApplication),
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

/// Perform the application of a rigid neutral to an argument.
fn apply_rigid<'db>(
    global: &GlobalEnv<'db>,
    rigid: &Rigid<'db>,
    arg: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    // If the operator is not pi-typed, bail.
    let Value::Pi(pi) = rigid.ty.as_ref() else {
        return Err(Error::BadApplication);
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
    let new_rigid = Rigid::new(rigid.head, spine, target_ty);
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
        return Err(Error::BadApplication);
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

fn eval_case<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    case: &syn::Case<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Evaluate the scrutinee expression
    let scrutinee = eval(env, &case.expr)?;
    let motive = Closure::new(env.local.clone(), case.motive.clone());
    let branches = case
        .branches
        .iter()
        .map(|branch| {
            let body = Closure::new(env.local.clone(), branch.body.clone());
            dom::CaseBranch::new(branch.constructor, branch.arity, body)
        })
        .collect();
    run_case(&env.global, scrutinee, motive, branches)
}

fn run_case<'db>(
    global: &GlobalEnv<'db>,
    scrutinee: Rc<Value<'db>>,
    motive: Closure<'db>,
    branches: Vec<dom::CaseBranch<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    match scrutinee.as_ref() {
        Value::DataConstructor(scrutinee) => {
            run_case_on_data_constructor(global, scrutinee, branches)
        }
        Value::Rigid(rigid) => {
            run_case_on_rigid(global, scrutinee.clone(), rigid, motive, branches)
        }
        Value::Flex(flex) => run_case_on_flex(global, scrutinee.clone(), flex, motive, branches),
        _ => Err(Error::BadCase),
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
    Err(Error::BadCase)
}

fn run_case_on_rigid<'db>(
    global: &GlobalEnv<'db>,
    scrutinee: Rc<Value<'db>>,
    rigid: &Rigid<'db>,
    motive: Closure<'db>,
    branches: Vec<dom::CaseBranch<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    // Verify that the type is a type constructor.
    let Value::TypeConstructor(type_constructor) = rigid.ty.as_ref() else {
        return Err(Error::BadCase);
    };
    let constructor = type_constructor.constructor;

    // Look up the type information from the global environment.
    let type_info = global
        .type_constructor(constructor)
        .map_err(|_| Error::UnknownTypeConstructor)?;

    // Get the parameters and indices off of the types.
    let num_parameters = type_info.num_parameters();
    let parameters = &type_constructor.arguments[..num_parameters];
    let indices = &type_constructor.arguments[num_parameters..];

    // Calculate the final type of the case statement.
    let mut motive_args = indices.to_vec();
    motive_args.push(scrutinee);
    let final_ty = run_closure(&global, &motive, motive_args)?;

    // Build the case eliminator.
    let eliminator = Eliminator::case(constructor, parameters.to_vec(), motive, branches);

    // Extend the spine with the case.
    let mut spine = rigid.spine.clone();
    spine.push(eliminator);

    // Create the new rigid neutral.
    let new_rigid = Rigid::new(rigid.head, spine, final_ty);
    Ok(Rc::new(Value::Rigid(new_rigid)))
}

fn run_case_on_flex<'db>(
    global: &GlobalEnv<'db>,
    scrutinee: Rc<Value<'db>>,
    flex: &Flex<'db>,
    motive: Closure<'db>,
    branches: Vec<dom::CaseBranch<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    // Verify that the type is a type constructor.
    let Value::TypeConstructor(type_constructor) = flex.ty.as_ref() else {
        return Err(Error::BadCase);
    };
    let constructor = type_constructor.constructor;

    // Look up the type information from the global environment.
    let type_info = global
        .type_constructor(constructor)
        .map_err(|_| Error::UnknownTypeConstructor)?;

    // Get the parameters and indices off of the types.
    let num_parameters = type_info.num_parameters();
    let parameters = &type_constructor.arguments[..num_parameters];
    let indices = &type_constructor.arguments[num_parameters..];

    // Calculate the final type of the case statement.
    let mut motive_args = indices.to_vec();
    motive_args.push(scrutinee);
    let final_ty = run_closure(&global, &motive, motive_args)?;

    // Build the case eliminator.
    let eliminator = Eliminator::case(constructor, parameters.to_vec(), motive, branches);

    // Extend the spine with the case.
    let mut spine = flex.spine.clone();
    spine.push(eliminator);

    // Create the new flex neutral.
    let new_flex = Flex::new(flex.head.clone(), spine, final_ty);
    Ok(Rc::new(Value::Flex(new_flex)))
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
                eliminatee = run_case(
                    global,
                    eliminatee,
                    case.motive.clone(),
                    case.branches.clone(),
                )?;
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
    let mut env = Environment { global, local };
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
        global: global,
        local: LocalEnv::new(),
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
