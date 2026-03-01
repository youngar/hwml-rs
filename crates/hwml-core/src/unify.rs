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
use std::collections::HashMap;
use std::option::Option;
use std::rc::Rc;
use std::vec;

pub struct MetaContext<'db> {
    // A map from metavariables to their solutions, if available.
    table: Vec<Option<Rc<Value<'db>>>>,
}

impl<'db> MetaContext<'db> {
    /// Create a new empty MetaContext.
    pub fn new() -> MetaContext<'db> {
        MetaContext { table: Vec::new() }
    }

    /// Allocate a new metavariable ID.
    pub fn fresh_id(&mut self) -> MetaVariableId {
        let id = MetaVariableId(self.table.len());
        self.table.push(None);
        id
    }

    pub fn lookup(&self, MetaVariableId(idx): MetaVariableId) -> &Option<Rc<Value<'db>>> {
        &self.table[idx]
    }
}

/// Force the substitution of a metavariable with its solution, if possible,
/// executing any now-unblocked computations. Forcing does not descend into values
/// because we do not need to force under a constructor--we only need to force
/// up to the head.
fn force<'db>(
    global: &val::GlobalEnv<'db>,
    mctx: &MetaContext<'db>,
    mut value: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, eval::Error> {
    while let Value::Flex(flex) = &*value {
        match mctx.lookup(flex.head.id) {
            Some(solution) => {
                // First, apply the solution to the local substitution.
                // The solution is a closure that expects the substitution arguments.
                let mut result = solution.clone();
                for arg in flex.head.local.iter() {
                    result = eval::run_application(global, &result, arg.clone())?;
                }
                // Then apply the spine.
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
    Mismatch(Rc<Value<'db>>, Rc<Value<'db>>),
    MismatchSpine(val::Spine<'db>, val::Spine<'db>),
    MismatchEliminator(val::Eliminator<'db>, val::Eliminator<'db>),
    NonLinearApplication(val::Eliminator<'db>),
    BlockedSolution(val::Eliminator<'db>),
    OccursCheck(MetaVariableId),
    ScopingError(Rc<Value<'db>>),
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
            // TODO: do we have to rename the type?
            let arg_ty = rename(global, mctx, meta, renaming, &a.argument.ty)?;
            let arg_value = rename(global, mctx, meta, renaming, &a.argument.value)?;
            let arg_normal = val::Normal::new(arg_ty, arg_value);
            Ok(Eliminator::application(arg_normal))
        }
        Eliminator::Case(_c) => {
            // Currently don't support renaming cases - we currently need to
            // know the binder depth of the motive, and we are reading that
            // off the type.  We will probably rework the motive.
            todo!("rename case");
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
    value: &Rc<Value<'db>>,
) -> UnificationResult<'db, Rc<Value<'db>>> {
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
            Ok(Rc::new(Value::flex(
                flex.head.clone(),
                spine,
                flex.ty.clone(),
            )))
        }
        Value::Rigid(r) => {
            // Remap the spine variable.
            let Some(variable) = renaming.rename(r.head.level) else {
                return Err(UnificationError::ScopingError(value.clone()));
            };
            let spine = rename_spine(global, mctx, meta, renaming, &r.spine)?;
            Ok(Rc::new(Value::rigid(
                Variable::new(variable),
                spine,
                r.ty.clone(),
            )))
        }
        Value::Lambda(lam) => {
            // Rename all free variables in the lambda closure.
            let mut new_env = LocalEnv::new();
            for value in lam.body.local.iter() {
                new_env.push(rename(global, mctx, meta, renaming, value)?);
            }
            let clos = Closure::new(new_env, lam.body.term.clone());
            Ok(Rc::new(Value::lambda(clos)))
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
            Ok(Rc::new(Value::pi(source, clos)))
        }
        Value::TypeConstructor(type_constructor) => {
            // Rename all arguments.
            let mut new_args = Vec::new();
            for arg in type_constructor.arguments.iter() {
                new_args.push(rename(global, mctx, meta, renaming, arg)?);
            }
            Ok(Rc::new(Value::type_constructor(
                type_constructor.constructor,
                new_args,
            )))
        }
        Value::DataConstructor(data_constructor) => {
            // Rename all arguments.
            let mut new_args = Vec::new();
            for arg in data_constructor.arguments.iter() {
                new_args.push(rename(global, mctx, meta, renaming, arg)?);
            }
            Ok(Rc::new(Value::data_constructor(
                data_constructor.constructor,
                new_args,
            )))
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
    solution: Rc<Value<'db>>,
    ty: Rc<Value<'db>>,
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
        rhs_syntax = Syntax::lambda_rc(rhs_syntax);
    }

    println!("Solved metavariable: {:?}", rhs_syntax);

    // Evaluate the solution back to a value.
    let _rhs_value = eval::eval(
        &mut Environment {
            global,
            local: LocalEnv::new(),
        },
        &rhs_syntax,
    )
    .map_err(UnificationError::Eval)?;

    // Store the solution.
    meta_context.table[meta_variable.id.0] = Some(rhs);

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

/// Unify two Case eliminators
fn unify_case<'db>(
    db: &'db dyn salsa::Database,
    global: &val::GlobalEnv<'db>,
    mctx: &mut MetaContext<'db>,
    depth: usize,
    c1: &val::Case<'db>,
    c2: &val::Case<'db>,
) -> UnificationResult<'db, ()> {
    // Placeholder type for fresh variables (we don't track precise types in this unifier)
    let placeholder_ty = Rc::new(Value::universe(UniverseLevel::new(0)));

    // 1. Check type constructors match
    if c1.type_constructor != c2.type_constructor {
        // Use Mismatch with placeholder values to indicate the case mismatch
        let v1 = Rc::new(Value::Constant(c1.type_constructor));
        let v2 = Rc::new(Value::Constant(c2.type_constructor));
        return Err(UnificationError::Mismatch(v1, v2));
    }

    // 2. Check parameters count and unify pairwise
    if c1.parameters.len() != c2.parameters.len() {
        // Parameters count mismatch - report as spine mismatch
        return Err(UnificationError::MismatchSpine(
            val::Spine::empty(),
            val::Spine::empty(),
        ));
    }
    for (p1, p2) in c1.parameters.iter().zip(c2.parameters.iter()) {
        unify(db, global, mctx, depth, p1.clone(), p2.clone())?;
    }

    // 3. Unify motives by applying to a fresh variable
    let scrutinee_var = Rc::new(Value::variable(Level(depth), placeholder_ty.clone()));
    let motive1 = eval::run_closure(global, &c1.motive, [scrutinee_var.clone()])?;
    let motive2 = eval::run_closure(global, &c2.motive, [scrutinee_var])?;
    unify(db, global, mctx, depth + 1, motive1, motive2)?;

    // 4. Check branches count and unify each
    if c1.branches.len() != c2.branches.len() {
        return Err(UnificationError::MismatchSpine(
            val::Spine::empty(),
            val::Spine::empty(),
        ));
    }

    for (b1, b2) in c1.branches.iter().zip(c2.branches.iter()) {
        if b1.constructor != b2.constructor {
            let v1 = Rc::new(Value::Constant(b1.constructor));
            let v2 = Rc::new(Value::Constant(b2.constructor));
            return Err(UnificationError::Mismatch(v1, v2));
        }
        if b1.arity != b2.arity {
            return Err(UnificationError::MismatchSpine(
                val::Spine::empty(),
                val::Spine::empty(),
            ));
        }

        // Create fresh variables for constructor arguments
        let args: Vec<_> = (0..b1.arity)
            .map(|i| Rc::new(Value::variable(Level(depth + i), placeholder_ty.clone())))
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
    lhs: Rc<Value<'db>>,
    rhs: Rc<Value<'db>>,
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
            let var = Rc::new(Value::variable(Level::new(depth), p1.source.clone()));
            let p1_target = eval::run_closure(global, &p1.target, [var.clone()])?;
            let p2_target = eval::run_closure(global, &p2.target, [var])?;
            unify(db, global, mctx, depth + 1, p1_target, p2_target)
        }
        (Value::Lambda(l1), Value::Lambda(l2)) => {
            let var = Rc::new(Value::variable(
                // TODO: get the type.
                Level::new(depth),
                Rc::new(Value::universe(UniverseLevel::new(0))),
            ));
            let l1_body = eval::run_closure(global, &l1.body, [var.clone()])?;
            let l2_body = eval::run_closure(global, &l2.body, [var])?;
            unify(db, global, mctx, depth + 1, l1_body, l2_body)
        }
        (Value::Lambda(l1), t2) => {
            let var = Rc::new(Value::variable(
                Level::new(depth),
                Rc::new(Value::universe(UniverseLevel::new(0))),
            ));
            let l1_body = eval::run_closure(global, &l1.body, [var.clone()])?;
            let l2_body = eval::run_application(global, &t2, var)?;
            unify(db, global, mctx, depth + 1, l1_body, l2_body)
        }
        (t1, Value::Lambda(l2)) => {
            let var = Rc::new(Value::variable(
                Level::new(depth),
                Rc::new(Value::universe(UniverseLevel::new(0))),
            ));
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
            let var = Rc::new(Value::variable(Level::new(depth), h1.source.clone()));
            let h1_target = eval::run_closure(global, &h1.target, [var.clone()])?;
            let h2_target = eval::run_closure(global, &h2.target, [var])?;
            unify(db, global, mctx, depth + 1, h1_target, h2_target)
        }
        // Module - compare closure bodies under a fresh variable
        (Value::Module(m1), Value::Module(m2)) => {
            let var = Rc::new(Value::variable(Level::new(depth), Rc::new(Value::bit())));
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
            // Check that the type constructor constants are the same.
            if t1.constructor != t2.constructor {
                return Err(UnificationError::Mismatch(lhs, rhs));
            }
            // Check that the arguments are the same.
            if t1.arguments.len() != t2.arguments.len() {
                return Err(UnificationError::Mismatch(lhs, rhs));
            }
            for (l, r) in t1.iter().zip(t2.iter()) {
                unify(db, global, mctx, depth, l.clone(), r.clone())?;
            }
            Ok(())
        }
        (Value::DataConstructor(d1), Value::DataConstructor(d2)) => {
            // Check that the data constructor constants are the same.
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
    use crate::Database;

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

        fn parse(&self, s: &'db str) -> Rc<Syntax<'db>> {
            parse_syntax(self.db, s).expect("parse failed")
        }

        fn eval(&self, stx: &Syntax<'db>) -> Rc<Value<'db>> {
            let mut env = Environment {
                global: &self.global,
                local: LocalEnv::new(),
            };
            eval::eval(&mut env, stx).expect("eval failed")
        }

        fn parse_eval(&self, s: &'db str) -> Rc<Value<'db>> {
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
            .unify_terms(&mut mctx, "HardwareType", "HardwareType")
            .is_ok());
        assert!(c.unify_terms(&mut mctx, "SignalType", "SignalType").is_ok());
        assert!(c.unify_terms(&mut mctx, "ModuleType", "ModuleType").is_ok());
        // Different hardware universes should fail
        assert!(c
            .unify_terms(&mut mctx, "HardwareType", "SignalType")
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
}
