use crate::common::*;
use crate::eval;
use crate::val::{self, Value};
use std::option::Option;
use std::rc::Rc;

pub struct MetaContext<'db> {
    // A map from metavariables to their solutions, if available.
    table: Vec<Option<Rc<Value<'db>>>>,
}

impl<'db> MetaContext<'db> {
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
    x: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, eval::Error> {
    match &*x {
        Value::Flex(f) => match mctx.lookup(f.head.id) {
            Some(t) => force(global, mctx, eval::run_spine(global, t.clone(), &f.spine)?),
            None => Ok(x),
        },
        _ => Ok(x),
    }
}

/// A partial renaming from context gamma to delta.
struct Renaming {
    /// Size of gamma.
    dom_len: Level,
    /// Size of delta.
    cod_len: Level,
    map: Vec<usize>,
}

impl Renaming {
    // fn lift(&self)
}

fn solve<'db>(
    global: &val::GlobalEnv<'db>,
    meta_context: &MetaContext<'db>,
    depth: usize,
    meta_variable: &val::MetaVariable<'db>,
    spine: &val::Spine<'db>,
    solution: Rc<Value>,
) {
    todo!();
}

pub enum UnificationError<'db> {
    Eval(eval::Error),
    Mismatch(Rc<Value<'db>>, Rc<Value<'db>>),
    MismatchSpine(val::Spine<'db>, val::Spine<'db>),
    MismatchEliminator(val::Eliminator<'db>, val::Eliminator<'db>),
}

impl<'db> From<eval::Error> for UnificationError<'db> {
    fn from(e: eval::Error) -> Self {
        UnificationError::Eval(e)
    }
}

pub type UnificationResult<'db> = Result<(), UnificationError<'db>>;

pub fn unify_elim<'db>(
    global: &val::GlobalEnv<'db>,
    mctx: &MetaContext<'db>,
    depth: usize,
    lhs: &val::Eliminator<'db>,
    rhs: &val::Eliminator<'db>,
) -> UnificationResult<'db> {
    match (lhs, rhs) {
        (val::Eliminator::Application(a1), val::Eliminator::Application(a2)) => unify(
            global,
            mctx,
            depth,
            a1.argument.value.clone(),
            a2.argument.value.clone(),
        ),
        (val::Eliminator::Case(c1), val::Eliminator::Case(c2)) => {
            todo!("implement unification for cases.")
        }
        (e1, e2) => Err(UnificationError::MismatchEliminator(e1.clone(), e2.clone())),
    }
}

pub fn unify_spine<'db>(
    global: &val::GlobalEnv<'db>,
    mctx: &MetaContext<'db>,
    depth: usize,
    lhs: &val::Spine<'db>,
    rhs: &val::Spine<'db>,
) -> UnificationResult<'db> {
    if lhs.len() != rhs.len() {
        return Err(UnificationError::MismatchSpine(lhs.clone(), rhs.clone()));
    }
    for (e1, e2) in lhs.iter().zip(rhs.iter()) {
        unify_elim(global, mctx, depth, e1, e2)?;
    }
    Ok(())
}

pub fn unify<'db>(
    global: &val::GlobalEnv<'db>,
    mctx: &MetaContext<'db>,
    depth: usize,
    lhs: Rc<Value<'db>>,
    rhs: Rc<Value<'db>>,
) -> UnificationResult<'db> {
    let lhs = force(global, mctx, lhs)?;
    let rhs = force(global, mctx, rhs)?;
    match (&*lhs, &*rhs) {
        (Value::Constant(c1), Value::Constant(c2)) => todo!(),
        (Value::Pi(p1), Value::Pi(p2)) => todo!(),
        (Value::Lambda(l1), Value::Lambda(l2)) => todo!(),
        (Value::Universe(u1), Value::Universe(u2)) => todo!(),
        (Value::TypeConstructor(t1), Value::TypeConstructor(t2)) => todo!(),
        (Value::DataConstructor(d1), Value::DataConstructor(d2)) => todo!(),
        (Value::Rigid(r1), Value::Rigid(r2)) => todo!(),
        (Value::Flex(f1), Value::Flex(f2)) => {
            if f1.head.id == f2.head.id {
                unify_spine(global, mctx, depth, &f1.spine, &f2.spine)
            } else {
                Ok(solve(global, mctx, depth, &f1.head, &f1.spine, rhs))
            }
        }
        (Value::Flex(f), _) => Ok(solve(global, mctx, depth, &f.head, &f.spine, rhs)),
        (_, Value::Flex(f)) => Ok(solve(global, mctx, depth, &f.head, &f.spine, lhs)),
        _ => Err(UnificationError::Mismatch(lhs, rhs)),
    }
}
