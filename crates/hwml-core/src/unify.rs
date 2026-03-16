use crate::binding::Binding;
use crate::common::*;
use crate::eval;
use crate::quote;
use crate::syn::Syntax;
use crate::val::Closure;
use crate::val::Eliminator;
use crate::val::Environment;
use crate::val::LocalEnv;
use crate::val::MetaVariable;
use crate::val::Variable;
use crate::val::{self, Value};
use crate::RcValue;
use std::collections::HashMap;
use std::option::Option;
use std::vec;

pub struct MetaContext<'db> {
    // A map from metavariables to their solutions, if available.
    table: HashMap<MetaVariableId, RcValue<'db>>,
}

impl<'db> MetaContext<'db> {
    /// Create a new empty MetaContext.
    pub fn new() -> MetaContext<'db> {
        MetaContext {
            table: HashMap::new(),
        }
    }

    /// Allocate a new metavariable ID.
    pub fn fresh_id(&mut self, local_index: u16) -> MetaVariableId {
        let id = MetaVariableId::new(local_index);
        // Don't insert a solution yet - it's unsolved
        id
    }

    pub fn lookup(&self, id: MetaVariableId) -> Option<&RcValue<'db>> {
        self.table.get(&id)
    }

    pub fn solve(&mut self, id: MetaVariableId, solution: RcValue<'db>) {
        self.table.insert(id, solution);
    }
}

fn force<'db>(
    global: &val::GlobalEnv<'db>,
    mctx: &MetaContext<'db>,
    mut value: RcValue<'db>,
) -> Result<RcValue<'db>, eval::Error> {
    while let Value::Flex(flex) = &*value {
        match mctx.lookup(flex.head.id) {
            Some(solution) => {
                let mut result = solution.clone();
                for arg in flex.head.local.iter() {
                    result = eval::run_application(global, &*result, arg.clone())?;
                }
                value = eval::run_spine(global, result, &flex.spine)?;
            }
            None => break,
        }
    }
    Ok(value)
}

#[derive(Debug)]
pub enum UnificationError<'db> {
    Eval(eval::Error),
    Quote(quote::Error<'db>),
    Mismatch(RcValue<'db>, RcValue<'db>),
    MismatchSpine(val::Spine<'db>, val::Spine<'db>),
    MismatchEliminator(val::Eliminator<'db>, val::Eliminator<'db>),
    NonLinearApplication(val::Eliminator<'db>),
    BlockedSolution(val::Eliminator<'db>),
    OccursCheck(MetaVariableId),
    ScopingError(RcValue<'db>),
}

type UnificationResult<'db, T> = Result<T, UnificationError<'db>>;

impl<'db> From<eval::Error> for UnificationError<'db> {
    fn from(e: eval::Error) -> Self {
        UnificationError::Eval(e)
    }
}

/// A partial renaming from context gamma (old context) to delta (new context).
#[derive(Clone)]
struct Renaming {
    /// Size of gamma.
    dom_len: usize,
    /// Size of delta.
    cod_len: usize,
    /// Mapping from delta vars to gamma vars.
    map: HashMap<Level, Level>,
}

impl Renaming {
    fn new() -> Renaming {
        Renaming {
            dom_len: 0,
            cod_len: 0,
            map: HashMap::new(),
        }
    }

    fn insert(&mut self, from: Level) {
        self.map.insert(from, Level::new(self.cod_len));
        self.cod_len += 1;
    }

    fn lift(&self) -> Renaming {
        let mut new_map = self.map.clone();
        new_map.insert(Level::new(self.cod_len), Level::new(self.dom_len));
        Renaming {
            dom_len: self.dom_len + 1,
            cod_len: self.cod_len + 1,
            map: new_map,
        }
    }

    fn rename(&self, level: Level) -> Option<Level> {
        self.map.get(&level).cloned()
    }
}

fn invert<'db>(
    global: &val::GlobalEnv<'db>,
    mctx: &MetaContext<'db>,
    depth: usize,
    spine: &val::Spine<'db>,
) -> UnificationResult<'db, Renaming> {
    let mut renaming = Renaming::new();
    renaming.cod_len = depth;
    for eliminator in spine.iter() {
        match eliminator {
            Eliminator::Application(a) => {
                let head = force(global, mctx, a.argument.value.clone())?;
                match &*head {
                    Value::Rigid(r) if r.spine.is_empty() => {
                        if renaming.map.contains_key(&r.head.level) {
                            return Err(UnificationError::NonLinearApplication(eliminator.clone()));
                        }
                        renaming.insert(r.head.level);
                    }
                    _ => return Err(UnificationError::BlockedSolution(eliminator.clone())),
                }
            }
            _ => return Err(UnificationError::BlockedSolution(eliminator.clone())),
        }
    }
    Ok(renaming)
}

fn rename_eliminator<'db>(
    global: &val::GlobalEnv<'db>,
    mctx: &MetaContext<'db>,
    meta: &val::MetaVariable<'db>,
    renaming: &mut Renaming,
    eliminator: &val::Eliminator<'db>,
) -> UnificationResult<'db, val::Eliminator<'db>> {
    match eliminator {
        Eliminator::Application(a) => {
            let arg_ty = rename(global, mctx, meta, renaming, &a.argument.ty)?;
            let arg_value = rename(global, mctx, meta, renaming, &a.argument.value)?;
            let arg_normal = val::Normal::new(arg_ty, arg_value);
            Ok(Eliminator::application(arg_normal))
        }
        Eliminator::Case(c) => {
            // Rename the case eliminator by renaming:
            // 1. All parameters (type constructor arguments)
            // 2. Each branch body (extending the renaming by the constructor's arity)

            // Rename all parameters
            let mut new_parameters = Vec::new();
            for param in c.parameters.iter() {
                new_parameters.push(rename(global, mctx, meta, renaming, param)?);
            }

            // Rename each branch
            let mut new_branches = Vec::new();
            for branch in c.branches.iter() {
                // Extend the renaming by the constructor's arity
                // Each constructor argument introduces a new binder
                let mut lifted_renaming = renaming.clone();
                for _ in 0..branch.arity {
                    lifted_renaming = lifted_renaming.lift();
                }

                // Rename all free variables in the branch closure
                let mut new_env = LocalEnv::new();
                for value in branch.body.local.iter() {
                    new_env.push(rename(global, mctx, meta, &mut lifted_renaming, value)?);
                }
                let new_body = Closure::new(new_env, branch.body.term.clone());

                new_branches.push(val::CaseBranch::new(
                    branch.constructor,
                    branch.arity,
                    new_body,
                ));
            }

            Ok(Eliminator::case(
                c.type_constructor,
                new_parameters,
                new_branches,
            ))
        }
    }
}

/// Rename all
fn rename_spine<'db>(
    global: &val::GlobalEnv<'db>,
    mctx: &MetaContext<'db>,
    meta: &MetaVariable<'db>,
    renaming: &mut Renaming,
    spine: &val::Spine<'db>,
) -> UnificationResult<'db, val::Spine<'db>> {
    let mut new_spine = vec![];
    for eliminator in spine.iter() {
        new_spine.push(rename_eliminator(global, mctx, meta, renaming, eliminator)?);
    }
    Ok(val::Spine::new(new_spine))
}

fn rename<'db>(
    global: &val::GlobalEnv<'db>,
    mctx: &MetaContext<'db>,
    meta: &val::MetaVariable<'db>,
    renaming: &mut Renaming,
    value: &RcValue<'db>,
) -> UnificationResult<'db, RcValue<'db>> {
    let value = force(global, mctx, value.clone())?;
    match &*value {
        Value::Flex(flex) => {
            // Perform the occurs check.  If the metavariable we are solving for
            // is in this term, we have an infinitely expanding term.
            if flex.head.id == meta.id {
                return Err(UnificationError::OccursCheck(meta.id));
            }
            // Replace the metavariable in the spine.
            let spine = rename_spine(global, mctx, meta, renaming, &flex.spine)?;
            Ok(Value::flex_rc(flex.head.clone(), spine, flex.ty.clone()))
        }
        Value::Rigid(r) => {
            // Remap the spine variable.
            let Some(variable) = renaming.rename(r.head.level) else {
                return Err(UnificationError::ScopingError(value.clone()));
            };
            let spine = rename_spine(global, mctx, meta, renaming, &r.spine)?;
            Ok(Value::rigid_rc(
                Variable::new(variable),
                spine,
                r.ty.clone(),
            ))
        }
        Value::Lambda(lam) => {
            // Rename all free variables in the lambda closure.
            let mut new_env = LocalEnv::new();
            for value in lam.body.local.iter() {
                new_env.push(rename(global, mctx, meta, renaming, value)?);
            }
            let clos = Closure::new(new_env, lam.body.term.clone());
            Ok(Value::lambda_rc(clos))
        }
        Value::Pi(pi) => {
            // Rename the source type.
            let source = rename(global, mctx, meta, renaming, &pi.source)?;
            // Rename all free variables in the pi closure.
            let mut lifted_renaming = renaming.lift();
            let mut new_env = LocalEnv::new();
            for value in pi.target.local.iter() {
                new_env.push(rename(global, mctx, meta, &mut lifted_renaming, value)?);
            }
            let clos = Closure::new(new_env, pi.target.term.clone());
            Ok(Value::pi_rc(source, clos))
        }
        Value::TypeConstructor(type_constructor) => {
            // Rename all arguments.
            let mut new_args = Vec::new();
            for arg in type_constructor.arguments.iter() {
                new_args.push(rename(global, mctx, meta, renaming, arg)?);
            }
            Ok(Value::type_constructor_rc(
                type_constructor.constructor,
                new_args,
            ))
        }
        Value::DataConstructor(data_constructor) => {
            // Rename all arguments.
            let mut new_args = Vec::new();
            for arg in data_constructor.arguments.iter() {
                new_args.push(rename(global, mctx, meta, renaming, arg)?);
            }
            Ok(Value::data_constructor_rc(
                data_constructor.constructor,
                new_args,
            ))
        }
        Value::EqType(eq) => {
            // Rename all components of the equality type
            let ty = rename(global, mctx, meta, renaming, &eq.ty)?;
            let lhs = rename(global, mctx, meta, renaming, &eq.lhs)?;
            let rhs = rename(global, mctx, meta, renaming, &eq.rhs)?;
            Ok(Value::eq_rc(ty, lhs, rhs))
        }
        Value::Refl(_) => {
            // Refl has no free variables to rename
            Ok(value.clone())
        }
        Value::Transport(transport) => {
            // Rename the motive closure
            let mut lifted_renaming = renaming.lift();
            let mut new_env = LocalEnv::new();
            for value in transport.motive.local.iter() {
                new_env.push(rename(global, mctx, meta, &mut lifted_renaming, value)?);
            }
            let motive = Closure::new(new_env, transport.motive.term.clone());
            // Rename proof and value
            let proof = rename(global, mctx, meta, renaming, &transport.proof)?;
            let value_renamed = rename(global, mctx, meta, renaming, &transport.value)?;
            Ok(Value::transport_rc(motive, proof, value_renamed))
        }
        _ => Ok(value.clone()),
    }
}

fn solve<'db>(
    _db: &'db dyn salsa::Database,
    global: &val::GlobalEnv<'db>,
    meta_context: &mut MetaContext<'db>,
    depth: usize,
    meta_variable: &val::MetaVariable<'db>,
    spine: &val::Spine<'db>,
    solution: RcValue<'db>,
    ty: RcValue<'db>,
) -> UnificationResult<'db, ()> {
    // Create an initial renamming from the spine.
    let mut renaming = invert(global, meta_context, depth, spine).unwrap();
    // Rename the solution.
    let rhs = rename(
        global,
        meta_context,
        meta_variable,
        &mut renaming,
        &solution,
    )?;

    // The number of binders we have to add.
    let depth = spine.len();

    // Quote the body back to syntax.
    let mut rhs_syntax = quote::quote(global, depth, &rhs, &ty).map_err(UnificationError::Quote)?;

    // Wrap the syntax in binders.
    for _ in 0..depth {
        rhs_syntax = Syntax::lambda_rc(Binding::new(rhs_syntax));
    }

    println!("Solved metavariable: {:?}", rhs_syntax);

    // Evaluate the solution back to a value.
    let _rhs_value = eval::eval(
        &mut Environment {
            global,
            local: LocalEnv::new(),
            transparent: val::TransparentEnv::new(),
        },
        &rhs_syntax,
    )
    .map_err(UnificationError::Eval)?;

    // Store the solution.
    meta_context.solve(meta_variable.id, rhs);

    // Ta-da!
    Ok(())
}

pub fn unify_elim<'db>(
    db: &'db dyn salsa::Database,
    global: &val::GlobalEnv<'db>,
    mctx: &mut MetaContext<'db>,
    depth: usize,
    lhs: &val::Eliminator<'db>,
    rhs: &val::Eliminator<'db>,
) -> UnificationResult<'db, ()> {
    match (lhs, rhs) {
        (val::Eliminator::Application(a1), val::Eliminator::Application(a2)) => unify(
            db,
            global,
            mctx,
            depth,
            a1.argument.value.clone(),
            a2.argument.value.clone(),
        ),
        (val::Eliminator::Case(c1), val::Eliminator::Case(c2)) => {
            unify_case(db, global, mctx, depth, c1, c2)
        }
        (e1, e2) => Err(UnificationError::MismatchEliminator(e1.clone(), e2.clone())),
    }
}

/// Unify two Case eliminators.
///
/// With the simple (non-dependent) return type design, we unify return types
/// directly rather than comparing motives.
fn unify_case<'db>(
    db: &'db dyn salsa::Database,
    global: &val::GlobalEnv<'db>,
    mctx: &mut MetaContext<'db>,
    depth: usize,
    c1: &val::Case<'db>,
    c2: &val::Case<'db>,
) -> UnificationResult<'db, ()> {
    let var_ty = Value::universe_rc(UniverseLevel::new(0));

    if c1.type_constructor != c2.type_constructor {
        let v1 = Value::constant_rc(c1.type_constructor);
        let v2 = Value::constant_rc(c2.type_constructor);
        return Err(UnificationError::Mismatch(v1, v2));
    }

    if c1.parameters.len() != c2.parameters.len() {
        return Err(UnificationError::MismatchSpine(
            val::Spine::empty(),
            val::Spine::empty(),
        ));
    }
    for (p1, p2) in c1.parameters.iter().zip(c2.parameters.iter()) {
        unify(db, global, mctx, depth, p1.clone(), p2.clone())?;
    }

    if c1.branches.len() != c2.branches.len() {
        return Err(UnificationError::MismatchSpine(
            val::Spine::empty(),
            val::Spine::empty(),
        ));
    }

    for (b1, b2) in c1.branches.iter().zip(c2.branches.iter()) {
        if b1.constructor != b2.constructor {
            let v1 = Value::constant_rc(b1.constructor);
            let v2 = Value::constant_rc(b2.constructor);
            return Err(UnificationError::Mismatch(v1, v2));
        }
        if b1.arity != b2.arity {
            return Err(UnificationError::MismatchSpine(
                val::Spine::empty(),
                val::Spine::empty(),
            ));
        }

        let args: Vec<_> = (0..b1.arity)
            .map(|i| Value::variable_rc(Level(depth + i), var_ty.clone()))
            .collect();
        let body1 = eval::run_closure(global, &b1.body, args.clone())?;
        let body2 = eval::run_closure(global, &b2.body, args)?;
        unify(db, global, mctx, depth + b1.arity, body1, body2)?;
    }

    Ok(())
}

pub fn unify_spine<'db>(
    db: &'db dyn salsa::Database,
    global: &val::GlobalEnv<'db>,
    mctx: &mut MetaContext<'db>,
    depth: usize,
    lhs: &val::Spine<'db>,
    rhs: &val::Spine<'db>,
) -> UnificationResult<'db, ()> {
    if lhs.len() != rhs.len() {
        return Err(UnificationError::MismatchSpine(lhs.clone(), rhs.clone()));
    }
    for (e1, e2) in lhs.iter().zip(rhs.iter()) {
        unify_elim(db, global, mctx, depth, e1, e2)?;
    }
    Ok(())
}

pub fn unify<'db>(
    db: &'db dyn salsa::Database,
    global: &val::GlobalEnv<'db>,
    mctx: &mut MetaContext<'db>,
    depth: usize,
    lhs: RcValue<'db>,
    rhs: RcValue<'db>,
) -> UnificationResult<'db, ()> {
    let lhs = force(global, mctx, lhs)?;
    let rhs = force(global, mctx, rhs)?;
    match (&*lhs, &*rhs) {
        (Value::Constant(c1), Value::Constant(c2)) => {
            if c1 != c2 {
                return Err(UnificationError::Mismatch(lhs, rhs));
            }
            Ok(())
        }
        (Value::Pi(p1), Value::Pi(p2)) => {
            unify(
                db,
                global,
                mctx,
                depth,
                p1.source.clone(),
                p2.source.clone(),
            )?;
            let var = Value::variable_rc(Level::new(depth), p1.source.clone());
            let p1_target = eval::run_closure(global, &p1.target, [var.clone()])?;
            let p2_target = eval::run_closure(global, &p2.target, [var])?;
            unify(db, global, mctx, depth + 1, p1_target, p2_target)
        }
        (Value::Lambda(l1), Value::Lambda(l2)) => {
            let var =
                Value::variable_rc(Level::new(depth), Value::universe_rc(UniverseLevel::new(0)));
            let l1_body = eval::run_closure(global, &l1.body, [var.clone()])?;
            let l2_body = eval::run_closure(global, &l2.body, [var])?;
            unify(db, global, mctx, depth + 1, l1_body, l2_body)
        }
        (Value::Lambda(l1), t2) => {
            let var =
                Value::variable_rc(Level::new(depth), Value::universe_rc(UniverseLevel::new(0)));
            let l1_body = eval::run_closure(global, &l1.body, [var.clone()])?;
            let l2_body = eval::run_application(global, &t2, var)?;
            unify(db, global, mctx, depth + 1, l1_body, l2_body)
        }
        (t1, Value::Lambda(l2)) => {
            let var =
                Value::variable_rc(Level::new(depth), Value::universe_rc(UniverseLevel::new(0)));
            let l1_body = eval::run_application(global, &t1, var.clone())?;
            let l2_body = eval::run_closure(global, &l2.body, [var])?;
            unify(db, global, mctx, depth + 1, l1_body, l2_body)
        }
        (Value::Universe(u1), Value::Universe(u2)) => {
            if u1.level != u2.level {
                return Err(UnificationError::Mismatch(lhs, rhs));
            }
            Ok(())
        }
        // Hardware universes - structural equality
        (Value::HardwareUniverse(_), Value::HardwareUniverse(_)) => Ok(()),
        (Value::SignalUniverse(_), Value::SignalUniverse(_)) => Ok(()),
        (Value::ModuleUniverse(_), Value::ModuleUniverse(_)) => Ok(()),
        // Bit type - structural equality
        (Value::Bit(_), Value::Bit(_)) => Ok(()),
        // Bit values - structural equality
        (Value::Zero(_), Value::Zero(_)) => Ok(()),
        (Value::One(_), Value::One(_)) => Ok(()),
        // HArrow - unify source and target (target is a closure)
        (Value::HArrow(h1), Value::HArrow(h2)) => {
            unify(
                db,
                global,
                mctx,
                depth,
                h1.source.clone(),
                h2.source.clone(),
            )?;
            // Target is a closure - run both under a fresh variable
            let var = Value::variable_rc(Level::new(depth), h1.source.clone());
            let h1_target = eval::run_closure(global, &h1.target, [var.clone()])?;
            let h2_target = eval::run_closure(global, &h2.target, [var])?;
            unify(db, global, mctx, depth + 1, h1_target, h2_target)
        }
        // Module - compare closure bodies under a fresh variable
        (Value::Module(m1), Value::Module(m2)) => {
            let var = Value::variable_rc(Level::new(depth), Value::bit_rc());
            let m1_body = eval::run_closure(global, &m1.body, [var.clone()])?;
            let m2_body = eval::run_closure(global, &m2.body, [var])?;
            unify(db, global, mctx, depth + 1, m1_body, m2_body)
        }
        // Lift types - unify the inner type
        (Value::Lift(l1), Value::Lift(l2)) => {
            unify(db, global, mctx, depth, l1.ty.clone(), l2.ty.clone())
        }
        // SLift types - unify the inner type
        (Value::SLift(s1), Value::SLift(s2)) => {
            unify(db, global, mctx, depth, s1.ty.clone(), s2.ty.clone())
        }
        // MLift types - unify the inner type
        (Value::MLift(m1), Value::MLift(m2)) => {
            unify(db, global, mctx, depth, m1.ty.clone(), m2.ty.clone())
        }
        (Value::TypeConstructor(t1), Value::TypeConstructor(t2)) => {
            if t1.constructor != t2.constructor {
                return Err(UnificationError::Mismatch(lhs, rhs));
            }
            if t1.arguments.len() != t2.arguments.len() {
                return Err(UnificationError::Mismatch(lhs, rhs));
            }
            for (l, r) in t1.iter().zip(t2.iter()) {
                unify(db, global, mctx, depth, l.clone(), r.clone())?;
            }
            Ok(())
        }
        (Value::DataConstructor(d1), Value::DataConstructor(d2)) => {
            if d1.constructor != d2.constructor {
                return Err(UnificationError::Mismatch(lhs, rhs));
            }
            if d1.arguments.len() != d2.arguments.len() {
                return Err(UnificationError::Mismatch(lhs, rhs));
            }
            for (l, r) in d1.iter().zip(d2.iter()) {
                unify(db, global, mctx, depth, l.clone(), r.clone())?;
            }
            Ok(())
        }
        (Value::EqType(eq1), Value::EqType(eq2)) => {
            unify(db, global, mctx, depth, eq1.ty.clone(), eq2.ty.clone())?;
            unify(db, global, mctx, depth, eq1.lhs.clone(), eq2.lhs.clone())?;
            unify(db, global, mctx, depth, eq1.rhs.clone(), eq2.rhs.clone())
        }
        (Value::Refl(_), Value::Refl(_)) => Ok(()),
        (Value::Transport(t1), Value::Transport(t2)) => {
            let var =
                Value::variable_rc(Level::new(depth), Value::universe_rc(UniverseLevel::new(0)));
            let m1_body = eval::run_closure(global, &t1.motive, [var.clone()])?;
            let m2_body = eval::run_closure(global, &t2.motive, [var])?;
            unify(db, global, mctx, depth + 1, m1_body, m2_body)?;
            unify(db, global, mctx, depth, t1.proof.clone(), t2.proof.clone())?;
            unify(db, global, mctx, depth, t1.value.clone(), t2.value.clone())
        }
        (Value::Rigid(r1), Value::Rigid(r2)) => {
            if r1.head.level != r2.head.level {
                return Err(UnificationError::Mismatch(lhs, rhs));
            }
            unify_spine(db, global, mctx, depth, &r1.spine, &r2.spine)
        }
        (Value::Flex(f1), Value::Flex(f2)) => {
            if f1.head.id == f2.head.id {
                // Same metavariable - first unify their substitutions (local environments)
                if f1.head.local.depth() != f2.head.local.depth() {
                    return Err(UnificationError::Mismatch(lhs, rhs));
                }
                for (v1, v2) in f1.head.local.iter().zip(f2.head.local.iter()) {
                    unify(db, global, mctx, depth, v1.clone(), v2.clone())?;
                }
                // Then unify their spines
                unify_spine(db, global, mctx, depth, &f1.spine, &f2.spine)
            } else {
                solve(
                    db,
                    global,
                    mctx,
                    depth,
                    &f1.head,
                    &f1.spine,
                    rhs,
                    f1.ty.clone(),
                )
            }
        }
        (Value::Flex(f), _) => solve(
            db,
            global,
            mctx,
            depth,
            &f.head,
            &f.spine,
            rhs,
            f.ty.clone(),
        ),
        (_, Value::Flex(f)) => solve(
            db,
            global,
            mctx,
            depth,
            &f.head,
            &f.spine,
            lhs,
            f.ty.clone(),
        ),
        _ => Err(UnificationError::Mismatch(lhs, rhs)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syn::parse::parse_syntax;
    use crate::{Database, RcSyntax};
    use std::rc::Rc;

    /// Test helper context
    struct Ctx<'db> {
        db: &'db Database,
        global: val::GlobalEnv<'db>,
    }

    impl<'db> Ctx<'db> {
        fn new(db: &'db Database) -> Self {
            Ctx {
                db,
                global: val::GlobalEnv::new(),
            }
        }

        fn parse(&self, s: &'db str) -> RcSyntax<'db> {
            parse_syntax(self.db, s).expect("parse failed")
        }

        fn eval(&self, stx: &Syntax<'db>) -> RcValue<'db> {
            let mut env = Environment {
                global: &self.global,
                local: LocalEnv::new(),
                transparent: val::TransparentEnv::new(),
            };
            eval::eval(&mut env, stx).expect("eval failed")
        }

        fn parse_eval(&self, s: &'db str) -> RcValue<'db> {
            let stx = self.parse(s);
            self.eval(&stx)
        }

        /// Unify two terms (as strings) and return Ok(()) if successful
        fn unify_terms(
            &self,
            mctx: &mut MetaContext<'db>,
            a: &'db str,
            b: &'db str,
        ) -> UnificationResult<'db, ()> {
            let va = self.parse_eval(a);
            let vb = self.parse_eval(b);
            unify(self.db, &self.global, mctx, 0, va, vb)
        }
    }

    // =========================================================================
    // Basic Unification Tests
    // =========================================================================

    #[test]
    fn test_unify_same_universe() {
        let db = Database::new();
        let c = Ctx::new(&db);
        let mut mctx = MetaContext::new();
        assert!(c.unify_terms(&mut mctx, "U0", "U0").is_ok());
        assert!(c.unify_terms(&mut mctx, "U1", "U1").is_ok());
    }

    #[test]
    fn test_unify_different_universes() {
        let db = Database::new();
        let c = Ctx::new(&db);
        let mut mctx = MetaContext::new();
        assert!(c.unify_terms(&mut mctx, "U0", "U1").is_err());
    }

    #[test]
    fn test_unify_same_bit() {
        let db = Database::new();
        let c = Ctx::new(&db);
        let mut mctx = MetaContext::new();
        assert!(c.unify_terms(&mut mctx, "Bit", "Bit").is_ok());
    }

    #[test]
    fn test_unify_bit_values() {
        let db = Database::new();
        let c = Ctx::new(&db);
        let mut mctx = MetaContext::new();
        assert!(c.unify_terms(&mut mctx, "0", "0").is_ok());
        assert!(c.unify_terms(&mut mctx, "1", "1").is_ok());
        assert!(c.unify_terms(&mut mctx, "0", "1").is_err());
    }

    #[test]
    fn test_unify_same_pi() {
        let db = Database::new();
        let c = Ctx::new(&db);
        let mut mctx = MetaContext::new();
        assert!(c
            .unify_terms(&mut mctx, "∀ (%x : U0) → U0", "∀ (%y : U0) → U0")
            .is_ok());
    }

    #[test]
    fn test_unify_different_pi() {
        let db = Database::new();
        let c = Ctx::new(&db);
        let mut mctx = MetaContext::new();
        assert!(c
            .unify_terms(&mut mctx, "∀ (%x : U0) → U0", "∀ (%y : U1) → U0")
            .is_err());
    }

    #[test]
    fn test_unify_same_harrow() {
        let db = Database::new();
        let c = Ctx::new(&db);
        let mut mctx = MetaContext::new();
        assert!(c.unify_terms(&mut mctx, "Bit → Bit", "Bit → Bit").is_ok());
    }

    // =========================================================================
    // Lambda/Eta Unification Tests
    // =========================================================================

    #[test]
    fn test_unify_lambdas() {
        let db = Database::new();
        let c = Ctx::new(&db);
        let mut mctx = MetaContext::new();
        // Two identity lambdas should unify
        assert!(c.unify_terms(&mut mctx, "λ %x → %x", "λ %y → %y").is_ok());
    }

    #[test]
    fn test_unify_different_lambdas() {
        let db = Database::new();
        let c = Ctx::new(&db);
        let mut mctx = MetaContext::new();
        // λx→x vs λx→U0 should fail
        assert!(c.unify_terms(&mut mctx, "λ %x → %x", "λ %y → U0").is_err());
    }

    // =========================================================================
    // Hardware Type Unification Tests
    // =========================================================================

    #[test]
    fn test_unify_hardware_universes() {
        let db = Database::new();
        let c = Ctx::new(&db);
        let mut mctx = MetaContext::new();
        assert!(c
            .unify_terms(&mut mctx, "HardwareUniverse", "HardwareUniverse")
            .is_ok());
        assert!(c
            .unify_terms(&mut mctx, "SignalUniverse", "SignalUniverse")
            .is_ok());
        assert!(c
            .unify_terms(&mut mctx, "ModuleUniverse", "ModuleUniverse")
            .is_ok());
        // Different hardware universes should fail
        assert!(c
            .unify_terms(&mut mctx, "HardwareUniverse", "SignalUniverse")
            .is_err());
    }

    #[test]
    fn test_unify_lift() {
        let db = Database::new();
        let c = Ctx::new(&db);
        let mut mctx = MetaContext::new();
        assert!(c.unify_terms(&mut mctx, "^Bit", "^Bit").is_ok());
        assert!(c.unify_terms(&mut mctx, "^U0", "^U0").is_ok());
    }

    #[test]
    fn test_unify_slift() {
        let db = Database::new();
        let c = Ctx::new(&db);
        let mut mctx = MetaContext::new();
        assert!(c.unify_terms(&mut mctx, "^sBit", "^sBit").is_ok());
    }

    #[test]
    fn test_unify_mlift() {
        let db = Database::new();
        let c = Ctx::new(&db);
        let mut mctx = MetaContext::new();
        assert!(c
            .unify_terms(&mut mctx, "^m(Bit → Bit)", "^m(Bit → Bit)")
            .is_ok());
    }

    // =========================================================================
    // Module Unification Tests
    // =========================================================================

    #[test]
    fn test_unify_modules() {
        let db = Database::new();
        let c = Ctx::new(&db);
        let mut mctx = MetaContext::new();
        // Two identity modules should unify
        assert!(c
            .unify_terms(&mut mctx, "mod %x → %x", "mod %y → %y")
            .is_ok());
    }

    #[test]
    fn test_unify_different_modules() {
        let db = Database::new();
        let c = Ctx::new(&db);
        let mut mctx = MetaContext::new();
        // mod x→x vs mod x→0 should fail
        assert!(c
            .unify_terms(&mut mctx, "mod %x → %x", "mod %y → 0")
            .is_err());
    }

    // =========================================================================
    // Axiom K / Deletion Rule Tests
    // =========================================================================

    /// Test the deletion rule: x = x succeeds trivially.
    ///
    /// This demonstrates Axiom K implicitly. In HoTT (without K), you cannot
    /// simply delete the constraint `x = x` because the proof `p : x = x`
    /// could be a non-trivial path/loop. With Axiom K, all proofs of `x = x`
    /// are equal to `refl`, so the constraint is trivially satisfiable.
    #[test]
    fn test_deletion_rule_axiom_k() {
        use crate::common::Level;

        let db = Database::new();
        let global = val::GlobalEnv::new();
        let mut mctx = MetaContext::new();

        // Create a rigid variable x at level 0
        let var = val::Variable {
            level: Level::new(0),
        };
        let var_ty = Value::universe_rc(UniverseLevel::new(0));
        let rigid_x = Value::rigid_rc(var.clone(), val::Spine::empty(), var_ty.clone());

        // Unify x with itself: x = x should succeed via deletion
        // This is the deletion rule: when both sides are the same rigid variable,
        // the constraint is trivially satisfied and can be deleted.
        let result = unify(&db, &global, &mut mctx, 1, rigid_x.clone(), rigid_x.clone());
        assert!(
            result.is_ok(),
            "x = x should succeed via deletion rule (Axiom K), got {:?}",
            result
        );
    }

    /// Test that deletion applies to rigid variables with matching spines.
    #[test]
    fn test_deletion_rule_with_spine() {
        use crate::common::Level;

        let db = Database::new();
        let global = val::GlobalEnv::new();
        let mut mctx = MetaContext::new();

        // Create a rigid variable f at level 0
        let var_f = val::Variable {
            level: Level::new(0),
        };
        let var_ty = Value::universe_rc(UniverseLevel::new(0));

        // Create an argument (rigid variable x at level 1)
        let var_x = val::Variable {
            level: Level::new(1),
        };
        let arg_x = Value::rigid_rc(var_x.clone(), val::Spine::empty(), var_ty.clone());

        // Create f(x) - rigid f with x in the spine
        // Application requires a Normal which has both type and value
        let arg_normal = val::Normal::new(var_ty.clone(), arg_x.clone());
        let spine = val::Spine::new(vec![val::Eliminator::Application(val::Application::new(
            arg_normal,
        ))]);
        let f_applied_x = Value::rigid_rc(var_f.clone(), spine, var_ty.clone());

        // Unify f(x) with f(x) - should succeed via deletion + spine unification
        let result = unify(
            &db,
            &global,
            &mut mctx,
            2,
            f_applied_x.clone(),
            f_applied_x.clone(),
        );
        assert!(
            result.is_ok(),
            "f(x) = f(x) should succeed via deletion rule, got {:?}",
            result
        );
    }

    // ========== Equality Type Unification Tests ==========

    #[test]
    fn test_unify_eq_types() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut mctx = MetaContext::new();

        // Eq Bit 0 1 ~ Eq Bit 0 1
        let eq1 = Value::eq(Value::bit_rc(), Value::zero_rc(), Value::one_rc());
        let eq2 = Value::eq(Value::bit_rc(), Value::zero_rc(), Value::one_rc());

        let result = unify(&db, &global, &mut mctx, 0, Rc::new(eq1), Rc::new(eq2));
        assert!(result.is_ok(), "Eq types should unify");
    }

    #[test]
    fn test_unify_eq_types_different_fails() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut mctx = MetaContext::new();

        // Eq Bit 0 1 ~ Eq Bit 1 0 should fail
        let eq1 = Value::eq(Value::bit_rc(), Value::zero_rc(), Value::one_rc());
        let eq2 = Value::eq(Value::bit_rc(), Value::one_rc(), Value::zero_rc());

        let result = unify(&db, &global, &mut mctx, 0, Rc::new(eq1), Rc::new(eq2));
        assert!(result.is_err(), "Different Eq types should not unify");
    }

    #[test]
    fn test_unify_refl() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut mctx = MetaContext::new();

        // refl ~ refl (Axiom K)
        let refl1 = Value::refl();
        let refl2 = Value::refl();

        let result = unify(&db, &global, &mut mctx, 0, Rc::new(refl1), Rc::new(refl2));
        assert!(result.is_ok(), "Refl should unify with refl (Axiom K)");
    }

    #[test]
    fn test_unify_transport() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut mctx = MetaContext::new();

        // transport (λ x → Bit) refl 0 ~ transport (λ x → Bit) refl 0
        let motive = Closure::new(val::LocalEnv::new(), Syntax::bit_rc());
        let transport1 = Value::transport(motive.clone(), Value::refl_rc(), Value::zero_rc());
        let transport2 = Value::transport(motive, Value::refl_rc(), Value::zero_rc());

        let result = unify(
            &db,
            &global,
            &mut mctx,
            0,
            Rc::new(transport1),
            Rc::new(transport2),
        );
        assert!(result.is_ok(), "Transport terms should unify");
    }
}
