use crate::{
    common::{Level, MetaVariableId},
    eval::{self, apply_Value, run_application, run_closure},
    syn::ConstantId,
    val::{
        self, Application, Case, DataConstructor, Eliminator, Environment, Flex, GlobalEnv, HArrow,
        LocalEnv, Normal, Pi, Rigid, Spine, Type, TypeConstructor, Universe, Value, Value,
    },
};
use itertools::izip;
use std::rc::Rc;

#[deny(elided_lifetimes_in_paths)]
pub enum Error<'db> {
    NotConvertible,
    LookupError(val::LookupError<'db>),
    EvalError(eval::Error),
}

impl<'db> From<eval::Error> for Error<'db> {
    fn from(err: eval::Error) -> Self {
        Error::EvalError(err)
    }
}

type Result<'db> = std::result::Result<(), Error<'db>>;

pub fn convertible<'db, T>(globals: &GlobalEnv<'db>, depth: usize, lhs: &T, rhs: &T) -> Result<'db>
where
    T: Convertible<'db>,
{
    lhs.is_convertible(globals, depth, rhs)
}

pub trait Convertible<'db> {
    fn is_convertible(&self, global: &GlobalEnv<'db>, depth: usize, other: &Self) -> Result<'db>;
}

impl<'db> Convertible<'db> for ConstantId<'db> {
    fn is_convertible(
        &self,
        _global: &GlobalEnv<'db>,
        _depth: usize,
        other: &ConstantId<'db>,
    ) -> Result<'db> {
        if self == other {
            Ok(())
        } else {
            Err(Error::NotConvertible)
        }
    }
}

impl<'db> Convertible<'db> for MetaVariableId {
    fn is_convertible(
        &self,
        _global: &GlobalEnv<'db>,
        _depth: usize,
        other: &MetaVariableId,
    ) -> Result<'db> {
        if self == other {
            Ok(())
        } else {
            Err(Error::NotConvertible)
        }
    }
}

impl<'db> Convertible<'db> for Level {
    fn is_convertible(
        &self,
        _global: &GlobalEnv<'db>,
        _depth: usize,
        other: &Level,
    ) -> Result<'db> {
        if self == other {
            Ok(())
        } else {
            Err(Error::NotConvertible)
        }
    }
}

impl<'db> Convertible<'db> for Universe {
    fn is_convertible(&self, _global: &GlobalEnv<'db>, _depth: usize, other: &Self) -> Result<'db> {
        if self.level == other.level {
            Ok(())
        } else {
            Err(Error::NotConvertible)
        }
    }
}

// ============================================================================
// HardwareUniverse Type Equality
// ============================================================================

impl<'db> Convertible<'db> for Type {
    fn is_convertible(
        &self,
        _global: &GlobalEnv<'db>,
        _depth: usize,
        _other: &Self,
    ) -> Result<'db> {
        // Type is a unit type, so all instances are equal
        Ok(())
    }
}

impl<'db> Convertible<'db> for HArrow<'db> {
    fn is_convertible(&self, global: &GlobalEnv<'db>, depth: usize, other: &Self) -> Result<'db> {
        // Check that source and target hardware types are convertible
        is_hwtype_convertible(global, depth, &self.source, &other.source)?;
        is_hwtype_convertible(global, depth, &self.target, &other.target)
    }
}

/// Check convertibility of hardware types (values of type Type).
pub fn is_hwtype_convertible<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        // Bit is equal to Bit
        (Value::Bit, Value::Bit) => Ok(()),

        // HardwareUniverse arrows are equal if their components are equal
        (Value::HArrow(lhs), Value::HArrow(rhs)) => lhs.is_convertible(global, depth, rhs),

        // Neutral hardware types (variables, metavariables, primitives)
        (Value::Rigid(lhs), Value::Rigid(rhs)) => lhs.is_convertible(global, depth, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => lhs.is_convertible(global, depth, rhs),
        (Value::Prim(lhs), Value::Prim(rhs)) => lhs.is_convertible(global, depth, rhs),

        _ => Err(Error::NotConvertible),
    }
}

impl<'db> Convertible<'db> for Normal<'db> {
    fn is_convertible(
        &self,
        global: &GlobalEnv<'db>,
        depth: usize,
        other: &Normal<'db>,
    ) -> Result<'db> {
        match (&*self.ty, &*other.ty) {
            (Value::Pi(lhs), Value::Pi(rhs)) => {
                let arg = Rc::new(Value::variable(Level::new(depth), lhs.source.clone()));
                let lnf = Normal::new(
                    run_closure(global, &lhs.target, [arg.clone()])?,
                    run_application(global, &self.value, arg.clone())?,
                );
                let rnf = Normal::new(
                    run_closure(global, &rhs.target, [arg.clone()])?,
                    run_application(global, &other.value, arg)?,
                );
                lnf.is_convertible(global, depth + 1, &rnf)
            }
            (Value::Universe(_), Value::Universe(_)) => {
                is_type_convertible(global, depth, &self.value, &other.value)
            }
            (Value::TypeConstructor(lhs), Value::TypeConstructor(_rhs)) => {
                is_type_constructor_instance_convertible(
                    global,
                    depth,
                    lhs.clone(),
                    &self.value,
                    &other.value,
                )
            }
            (Value::Rigid(_), Value::Rigid(_)) | (Value::Flex(_), Value::Flex(_)) => {
                is_neutral_instance_convertible(global, depth, &self.value, &other.value)
            }

            // HardwareUniverse types
            (Value::Type(_), Value::Type(_)) => {
                is_hwtype_convertible(global, depth, &self.value, &other.value)
            }
            (Value::Lift(hw_ty), Value::Lift(_)) => {
                // Pass the hardware type to enable type-directed comparison
                is_lift_instance_convertible(global, depth, hw_ty, &self.value, &other.value)
            }

            _ => Err(Error::NotConvertible),
        }
    }
}

pub fn is_neutral_instance_convertible<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
) -> Result<'db> {
    if let (Value::Rigid(lhs), Value::Rigid(rhs)) = (lhs, rhs) {
        return lhs.is_convertible(global, depth, rhs);
    }
    if let (Value::Flex(lhs), Value::Flex(rhs)) = (lhs, rhs) {
        return lhs.is_convertible(global, depth, rhs);
    }
    if let (Value::Prim(lhs), Value::Prim(rhs)) = (lhs, rhs) {
        return lhs.is_convertible(global, depth, rhs);
    }
    Err(Error::NotConvertible)
}

pub fn is_type_convertible<'a, 'db: 'a>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        (Value::Pi(lhs), Value::Pi(rhs)) => lhs.is_convertible(global, depth, rhs),
        (Value::TypeConstructor(lhs), Value::TypeConstructor(rhs)) => {
            lhs.is_convertible(global, depth, rhs)
        }
        (Value::Universe(lhs), Value::Universe(rhs)) => lhs.is_convertible(global, depth, rhs),
        (Value::Rigid(lhs), Value::Rigid(rhs)) => lhs.is_convertible(global, depth, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => lhs.is_convertible(global, depth, rhs),
        (Value::Prim(lhs), Value::Prim(rhs)) => lhs.is_convertible(global, depth, rhs),

        // HardwareUniverse types that can appear as meta-level types
        (Value::Lift(lhs), Value::Lift(rhs)) => is_hwtype_convertible(global, depth, lhs, rhs),

        _ => Err(Error::NotConvertible),
    }
}

/// Check convertibility of instances of lifted types (^ht).
/// These are hardware terms wrapped in Quote.
///
/// This function is type-directed: it uses the hardware type to determine
/// how to compare the values, enabling eta-equality for hardware functions.
pub fn is_lift_instance_convertible<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    hw_ty: &Value<'db>,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        // Quoted hardware terms: use type-directed comparison on the Values
        (Value::Quote(lhs_hval), Value::Quote(rhs_hval)) => {
            is_Value_convertible(global, depth, hw_ty, lhs_hval, rhs_hval)
        }

        // Neutral values (variables, metavariables, primitives)
        (Value::Rigid(lhs), Value::Rigid(rhs)) => lhs.is_convertible(global, depth, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => lhs.is_convertible(global, depth, rhs),
        (Value::Prim(lhs), Value::Prim(rhs)) => lhs.is_convertible(global, depth, rhs),

        _ => Err(Error::NotConvertible),
    }
}

/// Check convertibility of hardware values at a given hardware type.
///
/// This is the hardware-level analog of Normal::is_convertible for meta-level values.
/// For hardware arrows, we apply both values to a fresh variable and compare the results
/// (eta-equality). For base types, we compare structurally.
pub fn is_Value_convertible<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    hw_ty: &Value<'db>,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
) -> Result<'db> {
    match hw_ty {
        // For hardware arrows, apply to fresh variable and compare results (eta)
        Value::HArrow(arrow) => {
            // Create a fresh hardware variable at the current depth
            let fresh_var = Rc::new(Value::hvariable(Level::new(depth)));

            // Apply both values to the fresh variable
            let lhs_result =
                apply_Value(global, lhs, fresh_var.clone()).map_err(|_| Error::NotConvertible)?;
            let rhs_result =
                apply_Value(global, rhs, fresh_var).map_err(|_| Error::NotConvertible)?;

            // Recursively compare at the target type, with incremented depth
            is_Value_convertible(global, depth + 1, &arrow.target, &lhs_result, &rhs_result)
        }

        // For base types (Bit) or neutral types, compare structurally
        Value::Bit | Value::Rigid(_) | Value::Flex(_) | Value::Prim(_) => {
            if lhs == rhs {
                Ok(())
            } else {
                Err(Error::NotConvertible)
            }
        }

        // Other types shouldn't appear as hardware types
        _ => Err(Error::NotConvertible),
    }
}

impl<'db> Convertible<'db> for Pi<'db> {
    fn is_convertible(
        &self,
        global: &GlobalEnv<'db>,
        depth: usize,
        other: &Pi<'db>,
    ) -> Result<'db> {
        is_type_convertible(global, depth, &self.source, &other.source)?;
        let arg = Rc::new(Value::variable(Level::new(depth), self.source.clone()));
        let self_target = run_closure(global, &self.target, [arg.clone()])?;
        let other_target = run_closure(global, &other.target, [arg])?;
        is_type_convertible(global, depth + 1, &self_target, &other_target)
    }
}

impl<'db> Convertible<'db> for TypeConstructor<'db> {
    fn is_convertible(&self, global: &GlobalEnv<'db>, depth: usize, other: &Self) -> Result<'db> {
        // Check that the constructor is the same.
        let constructor = self.constructor;
        if constructor != other.constructor {
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
        for (larg, rarg, syn_ty) in izip!(self.iter(), other.iter(), type_info.arguments.iter()) {
            // Evaluate the type of the current argument.
            let sem_ty = eval::eval(&mut env, &syn_ty)?;

            // Check that the arguments are convertible.
            Normal::new(sem_ty.clone(), larg.clone()).is_convertible(
                global,
                depth,
                &Normal::new(sem_ty, rarg.clone()),
            )?;

            // Push the semantic argument into the environment for subsequent iterations.
            env.push(larg.clone());
        }
        Ok(())
    }
}

impl<'db> Convertible<'db> for Rigid<'db> {
    fn is_convertible(&self, global: &GlobalEnv<'db>, depth: usize, other: &Self) -> Result<'db> {
        // Check that the heads are the same variable.
        self.head
            .level
            .is_convertible(global, depth, &other.head.level)?;

        // Check that the spines are convertible.
        self.spine.is_convertible(global, depth, &other.spine)
    }
}

impl<'db> Convertible<'db> for Flex<'db> {
    fn is_convertible(&self, global: &GlobalEnv<'db>, depth: usize, other: &Self) -> Result<'db> {
        // Check that the heads are the same metavariable.
        self.head.id.is_convertible(global, depth, &other.head.id)?;

        // Check that the local environments (substitutions) have the same depth.
        if self.head.local.depth() != other.head.local.depth() {
            return Err(Error::NotConvertible);
        }

        // Look up the metavariable info to get the types of the substitution arguments.
        let meta_info = global
            .metavariable(self.head.id)
            .map_err(|_| Error::NotConvertible)?;

        // Create an environment for evaluating the types of the substitution arguments.
        let mut env = Environment {
            global: global,
            local: LocalEnv::new(),
        };

        // Check that each pair of substitution values is convertible at its expected type.
        for ((lval, rval), syn_ty) in self
            .head
            .local
            .iter()
            .zip(other.head.local.iter())
            .zip(meta_info.arguments.iter())
        {
            // Evaluate the type of the current substitution argument.
            let sem_ty = eval::eval(&mut env, syn_ty)?;

            // Check that the substitution values are convertible.
            Normal::new(sem_ty.clone(), lval.clone()).is_convertible(
                global,
                depth,
                &Normal::new(sem_ty, rval.clone()),
            )?;

            // Push the semantic argument into the environment for subsequent iterations.
            env.push(lval.clone());
        }

        // Check that the spines are convertible.
        self.spine.is_convertible(global, depth, &other.spine)
    }
}

impl<'db> Convertible<'db> for Spine<'db> {
    fn is_convertible(&self, global: &GlobalEnv<'db>, depth: usize, other: &Self) -> Result<'db> {
        // Check that the spines have the same length.
        if self.len() != other.len() {
            return Err(Error::NotConvertible);
        }

        // Check that each eliminator is convertible.
        for (lhs, rhs) in self.iter().zip(other.iter()) {
            lhs.is_convertible(global, depth, rhs)?;
        }

        Ok(())
    }
}

impl<'db> Convertible<'db> for Eliminator<'db> {
    fn is_convertible(&self, global: &GlobalEnv<'db>, depth: usize, other: &Self) -> Result<'db> {
        match (self, other) {
            (Eliminator::Application(lhs), Eliminator::Application(rhs)) => {
                lhs.is_convertible(global, depth, rhs)
            }
            (Eliminator::Case(lhs), Eliminator::Case(rhs)) => {
                lhs.is_convertible(global, depth, rhs)
            }
            _ => Err(Error::NotConvertible),
        }
    }
}

impl<'db> Convertible<'db> for Application<'db> {
    fn is_convertible(&self, global: &GlobalEnv<'db>, depth: usize, other: &Self) -> Result<'db> {
        // Check that the arguments are convertible.
        self.argument.is_convertible(global, depth, &other.argument)
    }
}

impl<'db> Convertible<'db> for Case<'db> {
    fn is_convertible(&self, global: &GlobalEnv<'db>, depth: usize, other: &Self) -> Result<'db> {
        // Check that the type constructors are the same.
        if self.type_constructor != other.type_constructor {
            return Err(Error::NotConvertible);
        }

        // Look up the type constructor info.
        let type_info = global
            .type_constructor(self.type_constructor)
            .map_err(Error::LookupError)?
            .clone();

        // Check that the parameters are convertible.
        // Create an environment for evaluating the type of each parameter.
        let mut env = Environment {
            global: global,
            local: LocalEnv::new(),
        };

        for (lparam, rparam, syn_ty) in izip!(
            self.parameters.iter(),
            other.parameters.iter(),
            type_info.parameters().iter()
        ) {
            // Evaluate the type of the current parameter.
            let sem_ty = eval::eval(&mut env, syn_ty).map_err(Error::EvalError)?;

            // Check that the parameters are convertible.
            let lnorm = Normal::new(sem_ty.clone(), lparam.clone());
            let rnorm = Normal::new(sem_ty, rparam.clone());
            lnorm.is_convertible(global, depth, &rnorm)?;

            // Push the semantic parameter into the environment for subsequent iterations.
            env.push(lparam.clone());
        }

        // Check that the motives are convertible by applying them to fresh variables.
        // First, create variables for the indices.
        let index_bindings = type_info.indices().to_vec();
        let index_telescope = crate::syn::Telescope::from(index_bindings);
        let index_tys = eval::eval_telescope(global, self.parameters.clone(), &index_telescope)?;

        let mut motive_args = Vec::new();
        for ty in index_tys.types {
            motive_args.push(Rc::new(Value::variable(
                Level::new(depth + motive_args.len()),
                ty,
            )));
        }

        // Create a variable for the scrutinee.
        let scrutinee_ty = Rc::new(Value::type_constructor(
            self.type_constructor,
            // TODO: shouldn't this include the indices?
            self.parameters.clone(),
        ));
        let scrutinee_var = Rc::new(Value::variable(Level::new(depth), scrutinee_ty));
        motive_args.push(scrutinee_var);

        // Apply both motives to the same arguments.
        let motive_args_len = motive_args.len();
        let self_motive_result = eval::run_closure(global, &self.motive, motive_args.clone())?;
        let other_motive_result = eval::run_closure(global, &other.motive, motive_args)?;

        // Check that the motive results are convertible as types.
        is_type_convertible(
            global,
            depth + motive_args_len,
            &self_motive_result,
            &other_motive_result,
        )?;

        // Check that the branches are convertible.
        // First, check that we have the same number of branches.
        if self.branches.len() != other.branches.len() {
            return Err(Error::NotConvertible);
        }

        // Check each branch.
        for (lbranch, rbranch) in izip!(self.branches.iter(), other.branches.iter()) {
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
                eval::eval_telescope(global, self.parameters.clone(), &data_info.arguments)?;
            let mut dcon_args = Vec::new();
            for ty in dcon_arg_tys.types {
                dcon_args.push(Rc::new(Value::variable(
                    Level::new(depth + dcon_args.len()),
                    ty,
                )));
            }

            // Evaluate the type of the data constructor to get the type constructor instance.
            let mut dcon_env = LocalEnv::new();
            dcon_env.extend(self.parameters.clone());
            let dcon_ty_clos = val::Closure::new(dcon_env, data_info.ty.clone());
            let dcon_ty = eval::run_closure(global, &dcon_ty_clos, dcon_args.clone())?;
            let Value::TypeConstructor(tcon) = &*dcon_ty else {
                return Err(Error::NotConvertible);
            };

            // Create the data constructor value.
            let dcon_val = Rc::new(Value::data_constructor(
                lbranch.constructor,
                dcon_args.clone(),
            ));

            // Create the arguments to the motive for this branch.
            let mut branch_motive_args = tcon.arguments[type_info.num_parameters()..].to_vec();
            branch_motive_args.push(dcon_val);

            // Evaluate the motive to get the type of the branch body.
            let branch_ty = eval::run_closure(global, &self.motive, branch_motive_args)?;

            // Apply both branch bodies to the same data constructor arguments.
            let lbranch_val = eval::run_closure(global, &lbranch.body, dcon_args.clone())?;
            let rbranch_val = eval::run_closure(global, &rbranch.body, dcon_args)?;

            // Check that the branch values are convertible.
            Normal::new(branch_ty.clone(), lbranch_val).is_convertible(
                global,
                depth + lbranch.arity,
                &Normal::new(branch_ty, rbranch_val),
            )?;
        }

        Ok(())
    }
}

fn is_data_constructor_convertible<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    ty: TypeConstructor<'db>,
    lhs: &DataConstructor<'db>,
    rhs: &DataConstructor<'db>,
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

        // TODO: substitute the second val into the second type and assert that the values
        // are the exact same. This should not be necessary for conversion checking.

        let lnorm = Normal::new(sem_ty.clone(), larg.clone());
        let rnorm = Normal::new(sem_ty, rarg.clone());
        lnorm.is_convertible(&global, depth, &rnorm)?;

        // Push the semantic argument into the environment for subsequent iterations.
        env.push(larg.clone());
    }
    Ok(())
}

// Check that the arguments are convertible.
pub fn is_type_constructor_instance_convertible<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    ty: TypeConstructor<'db>,
    lhs: &Value<'db>,
    rhs: &Value<'db>,
) -> Result<'db> {
    match (lhs, rhs) {
        (Value::DataConstructor(lhs), Value::DataConstructor(rhs)) => {
            is_data_constructor_convertible(global, depth, ty, lhs, rhs)
        }
        (Value::Rigid(lhs), Value::Rigid(rhs)) => lhs.is_convertible(global, depth, rhs),
        (Value::Flex(lhs), Value::Flex(rhs)) => lhs.is_convertible(global, depth, rhs),
        (Value::Prim(lhs), Value::Prim(rhs)) => lhs.is_convertible(global, depth, rhs),
        _ => Err(Error::NotConvertible),
    }
}
