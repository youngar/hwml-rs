# Phase 1 Implementation: The Core Engine

This document contains the **exact Rust code** for Phase 1, ready to copy-paste and start implementing.

## Part 1: The Environment and Closures

```rust
// File: crates/hwml-core/src/nbe/env.rs

use crate::*;
use im::Vector;  // Immutable vector for cheap cloning
use std::rc::Rc;

/// The runtime environment holding evaluated local variables.
/// Uses `im::Vector` for O(1) cloning and O(log n) push/pop.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Env<'db> {
    /// Local variables, indexed by Level (not Index!)
    /// Level 0 is the first binding, Level 1 is the second, etc.
    pub locals: Vector<RcValue<'db>>,
}

impl<'db> Env<'db> {
    /// Create an empty environment
    pub fn new() -> Self {
        Env {
            locals: Vector::new(),
        }
    }
    
    /// Get the depth (number of bindings)
    pub fn depth(&self) -> usize {
        self.locals.len()
    }
    
    /// Push a new local variable
    pub fn push(&self, value: RcValue<'db>) -> Self {
        let mut new_env = self.clone();
        new_env.locals.push_back(value);
        new_env
    }
    
    /// Get a local variable by Level
    pub fn get(&self, level: Level) -> RcValue<'db> {
        self.locals[level.0].clone()
    }
    
    /// Extend the environment with multiple values
    pub fn extend(&self, values: impl IntoIterator<Item = RcValue<'db>>) -> Self {
        let mut new_env = self.clone();
        for value in values {
            new_env.locals.push_back(value);
        }
        new_env
    }
}

/// A suspended computation: an unevaluated body + the environment it was defined in.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Closure<'db> {
    /// The environment captured when the closure was created
    pub env: Env<'db>,
    /// The body with one additional free variable (Index 0)
    pub body: RcSyntax<'db>,
}

impl<'db> Closure<'db> {
    pub fn new(env: Env<'db>, body: RcSyntax<'db>) -> Self {
        Closure { env, body }
    }
    
    /// Apply the closure to a value
    pub fn apply(&self, global: &GlobalEnv<'db>, arg: RcValue<'db>) -> Result<RcValue<'db>, EvalError> {
        let extended_env = self.env.push(arg);
        eval(global, &extended_env, &self.body)
    }
}

/// A type closure: produces a type when applied to a value
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TyClosure<'db> {
    pub env: Env<'db>,
    pub body: RcTySyntax<'db>,
}

impl<'db> TyClosure<'db> {
    pub fn new(env: Env<'db>, body: RcTySyntax<'db>) -> Self {
        TyClosure { env, body }
    }
    
    pub fn apply(&self, global: &GlobalEnv<'db>, arg: RcValue<'db>) -> Result<RcTy<'db>, EvalError> {
        let extended_env = self.env.push(arg);
        eval_ty(global, &extended_env, &self.body)
    }
}

/// A stuck term: a rigid head applied to a spine of arguments
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Neutral<'db> {
    pub head: Head,
    pub spine: Vec<RcValue<'db>>,
}

/// The head of a neutral term
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Head {
    /// A bound variable (De Bruijn Level, NOT Index!)
    Var(Level),
    /// An unsolved metavariable
    Meta(MetaVariableId),
    /// An opaque global constant (constructor, postulate)
    Global(DefId),
}

/// Definition ID (interned in salsa)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DefId(pub usize);

/// Metavariable ID
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MetaVariableId(pub usize);

/// The kind of a global definition
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DefKind<'db> {
    /// Opaque: inductives, constructors, postulates
    /// These get stuck and become Neutral
    Opaque,
    
    /// Transparent: functions with bodies
    /// These unfold during evaluation
    Transparent(RcSyntax<'db>),
}

/// The global environment (interface to the salsa database)
pub struct GlobalEnv<'db> {
    pub db: &'db dyn Database,
}

impl<'db> GlobalEnv<'db> {
    pub fn new(db: &'db dyn Database) -> Self {
        GlobalEnv { db }
    }
    
    /// Get the kind of a definition
    pub fn def_kind(&self, id: DefId) -> DefKind<'db> {
        // TODO: Query the salsa database
        // For now, return a placeholder
        DefKind::Opaque
    }
    
    /// Get the solution for a metavariable (if solved)
    pub fn meta_solution(&self, id: MetaVariableId) -> Option<RcSyntax<'db>> {
        // TODO: Query the solver state
        None
    }
}

/// Evaluation errors
#[derive(Debug)]
pub enum EvalError {
    UnboundVariable(Level),
    NotAFunction,
    NotAPi,
    UnknownGlobal(DefId),
}
```

## Part 2: The Syntax Enum (Quadrant 1)

```rust
// File: crates/hwml-core/src/nbe/syntax.rs

use crate::*;
use std::rc::Rc;

pub type RcSyntax<'db> = Rc<Syntax<'db>>;

/// Syntactic terms and type codes (unevaluated)
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Syntax<'db> {
    // ========== Universe Codes ==========
    UniverseCode(usize),
    SignalUniverseCode,
    ModuleUniverseCode,
    
    // ========== Type Codes ==========
    PiCode(RcSyntax<'db>, Binder<'db>),
    BitCode,
    
    // ========== Values/Computations ==========
    Lam(Binder<'db>),
    App(RcSyntax<'db>, RcSyntax<'db>),
    
    // ========== Case Expression ==========
    Case {
        scrutinee: RcSyntax<'db>,
        motive: Binder<'db>,  // The return type function
        branches: Vec<CaseBranch<'db>>,
    },
    
    // ========== Variables and References ==========
    Var(Index),
    Meta(MetaVariableId, Vec<RcSyntax<'db>>),
    Global(DefId),
    
    // ========== Hardware ==========
    HArrowCode(RcSyntax<'db>, RcSyntax<'db>),
    ModuleLam(Binder<'db>),
    HApp(RcSyntax<'db>, RcSyntax<'db>),
    Zero,
    One,
}

/// A binder that binds one variable
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Binder<'db> {
    pub name: Option<Name<'db>>,
    pub body: RcSyntax<'db>,
}

/// A case branch
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CaseBranch<'db> {
    pub constructor: DefId,
    pub arity: usize,
    pub body: RcSyntax<'db>,
}

/// De Bruijn Index (counts from the end, most recent = 0)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Index(pub usize);

impl Index {
    pub fn new(n: usize) -> Self {
        Index(n)
    }

    /// Convert to Level given the current depth
    pub fn to_level(&self, depth: usize) -> Level {
        Level(depth - self.0 - 1)
    }
}

/// De Bruijn Level (counts from the beginning, first = 0)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Level(pub usize);

impl Level {
    pub fn new(n: usize) -> Self {
        Level(n)
    }

    /// Convert to Index given the current depth
    pub fn to_index(&self, depth: usize) -> Index {
        Index(depth - self.0 - 1)
    }
}
```

## Part 3: The Value Enum (Quadrant 2)

```rust
// File: crates/hwml-core/src/nbe/value.rs

use crate::*;
use std::rc::Rc;

pub type RcValue<'db> = Rc<Value<'db>>;

/// Semantic values (evaluated, in WHNF)
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Value<'db> {
    // ========== Universe Codes (Evaluated) ==========
    UniverseCode(usize),
    SignalUniverseCode,
    ModuleUniverseCode,

    // ========== Type Codes (Evaluated) ==========
    PiCode(RcValue<'db>, Rc<Closure<'db>>),
    BitCode,

    // ========== Values ==========
    Lam(Rc<Closure<'db>>),

    // ========== Stuck Terms ==========
    /// A neutral term: a variable/meta/constructor applied to arguments
    Neutral(Rc<Neutral<'db>>),

    // ========== Hardware ==========
    HArrowCode(RcValue<'db>, RcValue<'db>),
    ModuleLam(Rc<Closure<'db>>),
    Zero,
    One,
}

impl<'db> Value<'db> {
    /// Create a fresh variable at the given level
    pub fn var(level: Level) -> RcValue<'db> {
        Rc::new(Value::Neutral(Rc::new(Neutral {
            head: Head::Var(level),
            spine: Vec::new(),
        })))
    }
}
```

## Part 4: The Evaluator (The Heart of NbE)

```rust
// File: crates/hwml-core/src/nbe/eval.rs

use crate::*;
use std::rc::Rc;

/// Evaluate a term to a value
pub fn eval<'db>(
    global: &GlobalEnv<'db>,
    env: &Env<'db>,
    term: &Syntax<'db>,
) -> Result<RcValue<'db>, EvalError> {
    match term {
        // ========== Universe Codes ==========
        Syntax::UniverseCode(n) => {
            Ok(Rc::new(Value::UniverseCode(*n)))
        }
        Syntax::SignalUniverseCode => {
            Ok(Rc::new(Value::SignalUniverseCode))
        }
        Syntax::ModuleUniverseCode => {
            Ok(Rc::new(Value::ModuleUniverseCode))
        }

        // ========== Type Codes ==========
        Syntax::PiCode(dom, cod) => {
            let dom_val = eval(global, env, dom)?;
            let closure = Closure::new(env.clone(), cod.body.clone());
            Ok(Rc::new(Value::PiCode(dom_val, Rc::new(closure))))
        }
        Syntax::BitCode => {
            Ok(Rc::new(Value::BitCode))
        }
        Syntax::HArrowCode(src, tgt) => {
            let src_val = eval(global, env, src)?;
            let tgt_val = eval(global, env, tgt)?;
            Ok(Rc::new(Value::HArrowCode(src_val, tgt_val)))
        }

        // ========== Lambda: Create a Closure ==========
        Syntax::Lam(binder) => {
            let closure = Closure::new(env.clone(), binder.body.clone());
            Ok(Rc::new(Value::Lam(Rc::new(closure))))
        }
        Syntax::ModuleLam(binder) => {
            let closure = Closure::new(env.clone(), binder.body.clone());
            Ok(Rc::new(Value::ModuleLam(Rc::new(closure))))
        }

        // ========== Application: Evaluate and Apply ==========
        Syntax::App(fun, arg) => {
            let fun_val = eval(global, env, fun)?;
            let arg_val = eval(global, env, arg)?;
            apply(global, &fun_val, arg_val)
        }
        Syntax::HApp(fun, arg) => {
            let fun_val = eval(global, env, fun)?;
            let arg_val = eval(global, env, arg)?;
            apply(global, &fun_val, arg_val)
        }

        // ========== Variable: Lookup in Environment ==========
        Syntax::Var(idx) => {
            // CRITICAL: Convert Index to Level!
            let level = idx.to_level(env.depth());
            Ok(env.get(level))
        }

        // ========== Metavariable: Check if Solved ==========
        Syntax::Meta(id, subst) => {
            // Evaluate the substitution (the local environment)
            let subst_val: Result<Vec<_>, _> = subst.iter()
                .map(|s| eval(global, env, s))
                .collect();
            let subst_val = subst_val?;

            // Check if the metavariable is solved
            if let Some(solution) = global.meta_solution(*id) {
                // Apply the solution to the substitution
                apply_spine(global, &solution, &subst_val)
            } else {
                // Unsolved: return as neutral with the spine
                Ok(Rc::new(Value::Neutral(Rc::new(Neutral {
                    head: Head::Meta(*id),
                    spine: subst_val,
                }))))
            }
        }

        // ========== Global: Unfold or Get Stuck ==========
        Syntax::Global(id) => {
            match global.def_kind(*id) {
                DefKind::Transparent(body) => {
                    // Unfold the definition and continue evaluating
                    eval(global, &Env::new(), &body)
                }
                DefKind::Opaque => {
                    // Opaque constant: becomes neutral
                    Ok(Rc::new(Value::Neutral(Rc::new(Neutral {
                        head: Head::Global(*id),
                        spine: Vec::new(),
                    }))))
                }
            }
        }

        // ========== Hardware Constants ==========
        Syntax::Zero => Ok(Rc::new(Value::Zero)),
        Syntax::One => Ok(Rc::new(Value::One)),

        // ========== Case Expression ==========
        Syntax::Case { scrutinee, motive, branches } => {
            let scrut_val = eval(global, env, scrutinee)?;
            eval_case(global, env, scrut_val, motive, branches)
        }
    }
}

/// Apply a function value to an argument
fn apply<'db>(
    global: &GlobalEnv<'db>,
    fun: &Value<'db>,
    arg: RcValue<'db>,
) -> Result<RcValue<'db>, EvalError> {
    match fun {
        // Lambda: apply the closure
        Value::Lam(closure) | Value::ModuleLam(closure) => {
            closure.apply(global, arg)
        }

        // Neutral: extend the spine (stuck application)
        Value::Neutral(neutral) => {
            let mut new_spine = neutral.spine.clone();
            new_spine.push(arg);
            Ok(Rc::new(Value::Neutral(Rc::new(Neutral {
                head: neutral.head,
                spine: new_spine,
            }))))
        }

        _ => Err(EvalError::NotAFunction),
    }
}

/// Apply a value to a spine of arguments
fn apply_spine<'db>(
    global: &GlobalEnv<'db>,
    fun: &Syntax<'db>,
    spine: &[RcValue<'db>],
) -> Result<RcValue<'db>, EvalError> {
    let mut result = eval(global, &Env::new(), fun)?;
    for arg in spine {
        result = apply(global, &result, arg.clone())?;
    }
    Ok(result)
}

/// Evaluate a case expression
fn eval_case<'db>(
    global: &GlobalEnv<'db>,
    env: &Env<'db>,
    scrutinee: RcValue<'db>,
    motive: &Binder<'db>,
    branches: &[CaseBranch<'db>],
) -> Result<RcValue<'db>, EvalError> {
    match scrutinee.as_ref() {
        // If scrutinee is a constructor applied to arguments, select the branch
        Value::Neutral(neutral) if matches!(neutral.head, Head::Global(_)) => {
            // TODO: Match on the constructor and evaluate the corresponding branch
            // For now, return stuck
            Ok(scrutinee)
        }

        // If scrutinee is stuck (variable, meta), the whole case is stuck
        Value::Neutral(_) => {
            // TODO: Create a stuck case expression
            Ok(scrutinee)
        }

        _ => Ok(scrutinee),
    }
}

/// Evaluate a type to a semantic type
pub fn eval_ty<'db>(
    global: &GlobalEnv<'db>,
    env: &Env<'db>,
    ty: &TySyntax<'db>,
) -> Result<RcTy<'db>, EvalError> {
    match ty {
        TySyntax::UniverseType => {
            Ok(Rc::new(Ty::UniverseType))
        }
        TySyntax::SignalUniverseType => {
            Ok(Rc::new(Ty::SignalUniverseType))
        }
        TySyntax::ModuleUniverseType => {
            Ok(Rc::new(Ty::ModuleUniverseType))
        }

        TySyntax::Pi(dom, cod) => {
            let dom_ty = eval_ty(global, env, dom)?;
            let closure = TyClosure::new(env.clone(), cod.body.clone());
            Ok(Rc::new(Ty::Pi(dom_ty, Rc::new(closure))))
        }

        TySyntax::HArrow(src, tgt) => {
            let src_ty = eval_ty(global, env, src)?;
            let tgt_ty = eval_ty(global, env, tgt)?;
            Ok(Rc::new(Ty::HArrow(src_ty, tgt_ty)))
        }

        // The Tarski Bridge: evaluate the code, then wrap in El
        TySyntax::El(code) => {
            let code_val = eval(global, env, code)?;
            Ok(Rc::new(Ty::El(code_val)))
        }
        TySyntax::SignalEl(code) => {
            let code_val = eval(global, env, code)?;
            Ok(Rc::new(Ty::SignalEl(code_val)))
        }
        TySyntax::ModuleEl(code) => {
            let code_val = eval(global, env, code)?;
            Ok(Rc::new(Ty::ModuleEl(code_val)))
        }
    }
}
```

## Part 5: The Quotation Functions

```rust
// File: crates/hwml-core/src/nbe/quote.rs

use crate::*;
use std::rc::Rc;

/// Quote a value back to syntax
/// `depth` is the number of binders we've gone under
pub fn quote<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>, EvalError> {
    match value {
        // ========== Universe Codes ==========
        Value::UniverseCode(n) => {
            Ok(Rc::new(Syntax::UniverseCode(*n)))
        }
        Value::SignalUniverseCode => {
            Ok(Rc::new(Syntax::SignalUniverseCode))
        }
        Value::ModuleUniverseCode => {
            Ok(Rc::new(Syntax::ModuleUniverseCode))
        }

        // ========== Type Codes ==========
        Value::PiCode(dom, cod) => {
            let dom_syn = quote(global, depth, dom)?;

            // To quote a closure: apply it to a fresh variable
            let fresh_var = Value::var(Level::new(depth));
            let body_val = cod.apply(global, fresh_var)?;
            let body_syn = quote(global, depth + 1, &body_val)?;

            Ok(Rc::new(Syntax::PiCode(
                dom_syn,
                Binder {
                    name: None,
                    body: body_syn,
                },
            )))
        }
        Value::BitCode => {
            Ok(Rc::new(Syntax::BitCode))
        }
        Value::HArrowCode(src, tgt) => {
            let src_syn = quote(global, depth, src)?;
            let tgt_syn = quote(global, depth, tgt)?;
            Ok(Rc::new(Syntax::HArrowCode(src_syn, tgt_syn)))
        }

        // ========== Lambda ==========
        Value::Lam(closure) => {
            let fresh_var = Value::var(Level::new(depth));
            let body_val = closure.apply(global, fresh_var)?;
            let body_syn = quote(global, depth + 1, &body_val)?;

            Ok(Rc::new(Syntax::Lam(Binder {
                name: None,
                body: body_syn,
            })))
        }
        Value::ModuleLam(closure) => {
            let fresh_var = Value::var(Level::new(depth));
            let body_val = closure.apply(global, fresh_var)?;
            let body_syn = quote(global, depth + 1, &body_val)?;

            Ok(Rc::new(Syntax::ModuleLam(Binder {
                name: None,
                body: body_syn,
            })))
        }

        // ========== Neutral ==========
        Value::Neutral(neutral) => {
            quote_neutral(global, depth, neutral)
        }

        // ========== Hardware ==========
        Value::Zero => Ok(Rc::new(Syntax::Zero)),
        Value::One => Ok(Rc::new(Syntax::One)),
    }
}

/// Quote a neutral term
fn quote_neutral<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    neutral: &Neutral<'db>,
) -> Result<RcSyntax<'db>, EvalError> {
    // Quote the head
    let head_syn = match neutral.head {
        Head::Var(level) => {
            // Convert Level to Index
            let index = level.to_index(depth);
            Rc::new(Syntax::Var(index))
        }
        Head::Meta(id) => {
            // Quote the spine (the substitution)
            let subst: Result<Vec<_>, _> = neutral.spine.iter()
                .map(|arg| quote(global, depth, arg))
                .collect();
            Rc::new(Syntax::Meta(id, subst?))
        }
        Head::Global(id) => {
            Rc::new(Syntax::Global(id))
        }
    };

    // Apply the spine
    let mut result = head_syn;
    for arg in &neutral.spine {
        let arg_syn = quote(global, depth, arg)?;
        result = Rc::new(Syntax::App(result, arg_syn));
    }

    Ok(result)
}

/// Quote a semantic type back to type syntax
pub fn quote_ty<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    ty: &Ty<'db>,
) -> Result<RcTySyntax<'db>, EvalError> {
    match ty {
        Ty::UniverseType => {
            Ok(Rc::new(TySyntax::UniverseType))
        }
        Ty::SignalUniverseType => {
            Ok(Rc::new(TySyntax::SignalUniverseType))
        }
        Ty::ModuleUniverseType => {
            Ok(Rc::new(TySyntax::ModuleUniverseType))
        }

        Ty::Pi(dom, cod) => {
            let dom_syn = quote_ty(global, depth, dom)?;

            // Apply closure to fresh variable
            let fresh_var = Value::var(Level::new(depth));
            let body_ty = cod.apply(global, fresh_var)?;
            let body_syn = quote_ty(global, depth + 1, &body_ty)?;

            Ok(Rc::new(TySyntax::Pi(
                dom_syn,
                TyBinder {
                    name: None,
                    body: body_syn,
                },
            )))
        }

        Ty::HArrow(src, tgt) => {
            let src_syn = quote_ty(global, depth, src)?;
            let tgt_syn = quote_ty(global, depth, tgt)?;
            Ok(Rc::new(TySyntax::HArrow(src_syn, tgt_syn)))
        }

        // The Tarski Bridge: quote the code
        Ty::El(code) => {
            let code_syn = quote(global, depth, code)?;
            Ok(Rc::new(TySyntax::El(code_syn)))
        }
        Ty::SignalEl(code) => {
            let code_syn = quote(global, depth, code)?;
            Ok(Rc::new(TySyntax::SignalEl(code_syn)))
        }
        Ty::ModuleEl(code) => {
            let code_syn = quote(global, depth, code)?;
            Ok(Rc::new(TySyntax::ModuleEl(code_syn)))
        }
    }
}
```

## Part 6: Key Patterns Explained

### Pattern 1: Variable Lookup (Index → Level → Value)

```rust
// In eval:
Syntax::Var(idx) => {
    // Step 1: Convert Index to Level
    // Index counts from the end: 0 = most recent
    // Level counts from the beginning: 0 = first binding
    let level = idx.to_level(env.depth());

    // Step 2: Lookup in environment by Level
    Ok(env.get(level))
}

// Example:
// Context: [x:Nat, y:Nat, z:Nat]  (depth = 3)
// Syntax::Var(0) = z  (Index 0)
//   → Level(3 - 0 - 1) = Level(2)
//   → env.get(Level(2)) = value of z
```

### Pattern 2: Quoting a Closure (Apply to Fresh Variable)

```rust
// In quote:
Value::Lam(closure) => {
    // Step 1: Create a fresh variable at the current depth
    let fresh_var = Value::var(Level::new(depth));

    // Step 2: Apply the closure to get the body value
    let body_val = closure.apply(global, fresh_var)?;

    // Step 3: Quote the body (depth + 1 because we went under a binder)
    let body_syn = quote(global, depth + 1, &body_val)?;

    Ok(Rc::new(Syntax::Lam(Binder { body: body_syn })))
}
```

### Pattern 3: Neutral Application (Building the Spine)

```rust
// In apply:
Value::Neutral(neutral) => {
    // Can't reduce! Extend the spine
    let mut new_spine = neutral.spine.clone();
    new_spine.push(arg);

    Ok(Rc::new(Value::Neutral(Rc::new(Neutral {
        head: neutral.head,
        spine: new_spine,
    }))))
}

// Example: f x y where f is a variable
// eval(f) → Neutral { head: Var(0), spine: [] }
// apply(_, x) → Neutral { head: Var(0), spine: [x] }
// apply(_, y) → Neutral { head: Var(0), spine: [x, y] }
```

## Part 7: Testing the Evaluator

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval_identity() {
        // fun x => x
        let id = Syntax::Lam(Binder {
            name: None,
            body: Rc::new(Syntax::Var(Index::new(0))),
        });

        let global = GlobalEnv::new(/* db */);
        let env = Env::new();

        let result = eval(&global, &env, &id).unwrap();

        // Should be a lambda closure
        assert!(matches!(result.as_ref(), Value::Lam(_)));
    }

    #[test]
    fn test_eval_application() {
        // (fun x => x) zero
        let id = Rc::new(Syntax::Lam(Binder {
            name: None,
            body: Rc::new(Syntax::Var(Index::new(0))),
        }));
        let zero = Rc::new(Syntax::Zero);
        let app = Syntax::App(id, zero);

        let global = GlobalEnv::new(/* db */);
        let env = Env::new();

        let result = eval(&global, &env, &app).unwrap();

        // Should reduce to Zero
        assert!(matches!(result.as_ref(), Value::Zero));
    }
}
```

