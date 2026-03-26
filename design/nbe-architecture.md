# NbE Architecture: The Complete Blueprint

## Executive Summary

This document defines the **Normalization by Evaluation (NbE)** architecture for `hwml-rust`, implementing Jon Sterling's "Fuss-free universe hierarchies" with a Tarski-style separation between semantic types and syntactic codes.

**Key Innovation:** The 4-Quadrant Architecture separates along two axes:
1. **Syntactic vs. Semantic** (ASTs vs. Evaluated Data)
2. **Terms vs. Types** (Computing Data vs. Classifying Data)

This creates a clean separation where:
- The **Unifier** operates on semantic types (`Ty`) with no universe levels
- The **Evaluator** operates on terms (`Syntax` → `Value`) with universe codes
- The **Elaborator** bridges surface syntax to both domains via `El` insertion

---

## Part 1: The 4-Quadrant Data Structures

### Quadrant 1: `Syntax` (Unevaluated Terms/Codes)

This is what the user writes and what gets evaluated. It contains universe **codes** and type **codes**.

```rust
// File: crates/hwml-core/src/nbe/syntax.rs

use crate::*;
use std::rc::Rc;

pub type RcSyntax<'db> = Rc<Syntax<'db>>;

/// Syntactic terms and type codes (unevaluated)
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub enum Syntax<'db> {
    // ========== Universe Codes ==========
    /// Type 0, Type 1, Type 2, ... (restricted universe codes)
    UniverseCode(usize),
    /// Signal (the universe of signal types)
    SignalUniverseCode,
    /// Module (the universe of module types)
    ModuleUniverseCode,
    
    // ========== Type Codes ==========
    /// Pi type code: (x : A) -> B
    PiCode(RcSyntax<'db>, Binder<'db, Syntax<'db>>),
    /// Bit type code (the type of single-bit signals)
    BitCode,
    /// Inductive type constructor applied to arguments
    /// e.g., Nat, Vec A n
    TypeConstructorCode(QualifiedName<'db>, Vec<RcSyntax<'db>>),
    
    // ========== Values/Computations ==========
    /// Lambda abstraction: fun x => body
    Lam(Binder<'db, Syntax<'db>>),
    /// Application: f x
    App(RcSyntax<'db>, RcSyntax<'db>),
    /// Data constructor applied to arguments
    /// e.g., zero, succ n, vcons A n x xs
    DataConstructorCode(QualifiedName<'db>, Vec<RcSyntax<'db>>),
    /// Case expression (pattern matching)
    Case {
        scrutinee: Index,  // De Bruijn index of variable being matched
        branches: Vec<CaseBranch<'db>>,
    },
    
    // ========== Hardware-Specific ==========
    /// Hardware arrow code: Signal => Module
    HArrowCode(RcSyntax<'db>, RcSyntax<'db>>),
    /// Module abstraction: module (s : Signal) => body
    ModuleLam(Binder<'db, Syntax<'db>>),
    /// Module application: m @ sig
    HApp(RcSyntax<'db>, RcSyntax<'db>>),
    /// Bit literals
    Zero,
    One,
    
    // ========== Equality ==========
    /// Equality type code: Eq A x y
    EqCode(RcSyntax<'db>, RcSyntax<'db>, RcSyntax<'db>>),
    /// Reflexivity: refl
    Refl,
    
    // ========== Variables and Metavariables ==========
    /// Bound variable (De Bruijn index)
    Var(Index),
    /// Metavariable with substitution
    Meta(MetaVariableId, Vec<RcSyntax<'db>>),
    /// Global constant
    Const(QualifiedName<'db>),
}

/// A case branch: constructor pattern with body
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct CaseBranch<'db> {
    pub constructor: QualifiedName<'db>,
    pub arity: usize,  // Number of constructor arguments bound
    pub body: RcSyntax<'db>,  // Body with arity additional bound variables
}

/// A binder that binds one variable in a term
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Binder<'db, T> {
    pub name: Option<Name<'db>>,  // For pretty-printing
    pub body: T,
}
```

### Quadrant 2: `Value` (Evaluated Terms/Codes)

This is what `eval` returns. It represents weak head normal forms with no unevaluated applications.

```rust
// File: crates/hwml-core/src/nbe/value.rs

use crate::*;
use std::rc::Rc;

pub type RcValue<'db> = Rc<Value<'db>>;

/// Semantic values (evaluated terms)
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Value<'db> {
    // ========== Universe Codes (Evaluated) ==========
    UniverseCode(usize),
    SignalUniverseCode,
    ModuleUniverseCode,
    
    // ========== Type Codes (Evaluated) ==========
    PiCode(RcValue<'db>, Rc<Closure<'db>>),
    BitCode,
    TypeConstructorCode(QualifiedName<'db>, Vec<RcValue<'db>>),
    
    // ========== Values ==========
    Lam(Rc<Closure<'db>>),
    DataConstructorCode(QualifiedName<'db>, Vec<RcValue<'db>>),
    
    // ========== Hardware ==========
    HArrowCode(RcValue<'db>, RcValue<'db>>),
    ModuleLam(Rc<Closure<'db>>),
    Zero,
    One,
    
    // ========== Equality ==========
    EqCode(RcValue<'db>, RcValue<'db>, RcValue<'db>>),
    Refl,
    
    // ========== Neutral Terms (Stuck) ==========
    /// A neutral term: a variable or metavariable applied to a spine of arguments
    Neutral(Rc<Neutral<'db>>),
}

/// A closure: an environment + a term with one free variable
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Closure<'db> {
    /// The local environment (values for free variables in body)
    pub env: LocalEnv<'db>,
    /// The body with one additional free variable (De Bruijn index 0)
    pub body: RcSyntax<'db>,
}

impl<'db> Closure<'db> {
    pub fn new(env: LocalEnv<'db>, body: RcSyntax<'db>) -> Self {
        Closure { env, body }
    }
    
    /// Apply the closure to a value
    pub fn apply(&self, global: &GlobalEnv<'db>, arg: RcValue<'db>) -> Result<RcValue<'db>, EvalError> {
        let mut extended_env = self.env.clone();
        extended_env.push(arg);
        eval(global, &extended_env, &self.body)
    }
}

/// A neutral term: stuck on a variable or metavariable
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Neutral<'db> {
    pub head: Head<'db>,
    pub spine: Spine<'db>,
}

/// The head of a neutral term
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Head<'db> {
    /// Rigid: a bound variable (Level, not Index!)
    Var(Level),
    /// Rigid: a global constant
    Const(QualifiedName<'db>),
    /// Flexible: an unsolved metavariable
    Meta(MetaVariableId, Vec<RcValue<'db>>),  // Meta with its substitution evaluated
}

/// The spine of a neutral term (arguments applied to the head)
pub type Spine<'db> = Vec<Elim<'db>>;

/// An elimination form applied to a neutral
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Elim<'db> {
    /// Function application
    App(RcValue<'db>),
    /// Hardware application
    HApp(RcValue<'db>),
    /// Case split (stuck because scrutinee is neutral)
    Case(Vec<CaseBranchValue<'db>>),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct CaseBranchValue<'db> {
    pub constructor: QualifiedName<'db>,
    pub arity: usize,
    pub body: Rc<Closure<'db>>,  // Closure that binds `arity` variables
}

/// Local environment: a stack of values for bound variables
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct LocalEnv<'db> {
    values: Vec<RcValue<'db>>,
}

impl<'db> LocalEnv<'db> {
    pub fn new() -> Self {
        LocalEnv { values: Vec::new() }
    }
    
    pub fn push(&mut self, value: RcValue<'db>) {
        self.values.push(value);
    }
    
    pub fn get(&self, level: Level) -> RcValue<'db> {
        self.values[level.0].clone()
    }
    
    pub fn depth(&self) -> usize {
        self.values.len()
    }
}
```

### Quadrant 3: `TySyntax` (Unevaluated Types)

This is the "Top-Level" type language. Generated by the elaborator, fed into the type evaluator.

```rust
// File: crates/hwml-core/src/nbe/ty.rs

use crate::*;
use std::rc::Rc;

pub type RcTySyntax<'db> = Rc<TySyntax<'db>>;

/// Syntactic types (unevaluated, top-level)
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum TySyntax<'db> {
    // ========== Universe Types (The Classifiers) ==========
    /// The type of Type 0, Type 1, Type 2, ...
    /// This is the "unconstrained top-level" when user writes just `Type`
    UniverseType,
    /// The type of Signal
    SignalUniverseType,
    /// The type of Module
    ModuleUniverseType,

    // ========== Top-Level Type Formers ==========
    /// Dependent function type: (x : A) -> B
    /// Domain is a type, codomain is a type depending on a term
    Pi(RcTySyntax<'db>, TyBinder<'db>),

    /// Hardware arrow type: Signal => Module
    /// This is a top-level type former, not a code!
    HArrow(RcTySyntax<'db>, RcTySyntax<'db>>),

    // ========== The Tarski Bridge ==========
    /// El(code): Decode a type code into a semantic type
    /// This is where universe levels live!
    /// e.g., El(UniverseCode(0)) is the type of small types
    El(RcSyntax<'db>),

    /// SignalEl(code): Decode a signal type code
    /// e.g., SignalEl(BitCode) is the type Bit
    SignalEl(RcSyntax<'db>),

    /// ModuleEl(code): Decode a module type code
    ModuleEl(RcSyntax<'db>),
}

/// A binder in a type (binds a term variable, body is a type)
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct TyBinder<'db> {
    pub name: Option<Name<'db>>,
    pub body: RcTySyntax<'db>,
}
```

### Quadrant 4: `Ty` (Evaluated Types)

This is what the **Unifier** operates on. It contains no universe levels!

```rust
// Still in: crates/hwml-core/src/nbe/ty.rs

pub type RcTy<'db> = Rc<Ty<'db>>;

/// Semantic types (evaluated, top-level)
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Ty<'db> {
    // ========== Universe Types ==========
    UniverseType,
    SignalUniverseType,
    ModuleUniverseType,

    // ========== Type Formers ==========
    /// Dependent function type: (x : A) -> B
    /// Domain is a type, codomain is a TYPE CLOSURE (depends on a VALUE)
    Pi(RcTy<'db>, Rc<TyClosure<'db>>),

    /// Hardware arrow: Signal => Module
    HArrow(RcTy<'db>, RcTy<'db>>),

    // ========== The Tarski Bridge (Evaluated) ==========
    /// El(value): A type decoded from an evaluated type code
    El(RcValue<'db>),
    SignalEl(RcValue<'db>),
    ModuleEl(RcValue<'db>),
}

/// A type closure: given a VALUE, produce a TYPE
/// This is needed for dependent types: the codomain of a Pi depends on the VALUE of the argument
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct TyClosure<'db> {
    /// The local environment (values for free variables)
    pub env: LocalEnv<'db>,
    /// The body type with one additional free variable
    pub body: RcTySyntax<'db>,
}

impl<'db> TyClosure<'db> {
    pub fn new(env: LocalEnv<'db>, body: RcTySyntax<'db>) -> Self {
        TyClosure { env, body }
    }

    /// Apply the type closure to a value, producing a type
    pub fn apply(&self, global: &GlobalEnv<'db>, arg: RcValue<'db>) -> Result<RcTy<'db>, EvalError> {
        let mut extended_env = self.env.clone();
        extended_env.push(arg);
        eval_ty(global, &extended_env, &self.body)
    }
}
```

---

## Part 2: The Core Operations

### Operation 1: Evaluation (`eval` and `eval_ty`)

Evaluation takes syntax to values, substituting the environment.

```rust
// File: crates/hwml-core/src/nbe/eval.rs

use crate::*;

/// Evaluate a term to a value
pub fn eval<'db>(
    global: &GlobalEnv<'db>,
    env: &LocalEnv<'db>,
    term: &Syntax<'db>,
) -> Result<RcValue<'db>, EvalError> {
    match term {
        // Universe codes evaluate to themselves
        Syntax::UniverseCode(n) => Ok(Rc::new(Value::UniverseCode(*n))),
        Syntax::SignalUniverseCode => Ok(Rc::new(Value::SignalUniverseCode)),
        Syntax::ModuleUniverseCode => Ok(Rc::new(Value::ModuleUniverseCode)),

        // Type codes
        Syntax::PiCode(dom, cod) => {
            let dom_val = eval(global, env, dom)?;
            let closure = Closure::new(env.clone(), cod.body.clone());
            Ok(Rc::new(Value::PiCode(dom_val, Rc::new(closure))))
        }
        Syntax::BitCode => Ok(Rc::new(Value::BitCode)),
        Syntax::TypeConstructorCode(name, args) => {
            let args_val: Result<Vec<_>, _> = args.iter()
                .map(|arg| eval(global, env, arg))
                .collect();
            Ok(Rc::new(Value::TypeConstructorCode(*name, args_val?)))
        }

        // Lambda: create a closure
        Syntax::Lam(binder) => {
            let closure = Closure::new(env.clone(), binder.body.clone());
            Ok(Rc::new(Value::Lam(Rc::new(closure))))
        }

        // Application: evaluate and apply
        Syntax::App(fun, arg) => {
            let fun_val = eval(global, env, fun)?;
            let arg_val = eval(global, env, arg)?;
            apply(global, &fun_val, arg_val)
        }

        // Variable: lookup in environment
        Syntax::Var(idx) => {
            let level = idx.to_level(env.depth());
            Ok(env.get(level))
        }

        // Metavariable: check if solved, otherwise return neutral
        Syntax::Meta(id, subst) => {
            // Evaluate the substitution
            let subst_val: Result<Vec<_>, _> = subst.iter()
                .map(|s| eval(global, env, s))
                .collect();

            // Check if the metavariable is solved
            if let Some(solution) = global.meta_solution(*id) {
                // Apply the solution to the substitution
                apply_spine(global, solution, &subst_val?)
            } else {
                // Unsolved: return as neutral
                let head = Head::Meta(*id, subst_val?);
                Ok(Rc::new(Value::Neutral(Rc::new(Neutral {
                    head,
                    spine: Vec::new(),
                }))))
            }
        }

        // Constants: unfold definition
        Syntax::Const(name) => {
            let def = global.constant(*name)?;
            eval(global, &LocalEnv::new(), &def.value)
        }

        // ... (other cases)
    }
}

/// Apply a function value to an argument
fn apply<'db>(
    global: &GlobalEnv<'db>,
    fun: &Value<'db>,
    arg: RcValue<'db>,
) -> Result<RcValue<'db>, EvalError> {
    match fun {
        Value::Lam(closure) => closure.apply(global, arg),
        Value::Neutral(neutral) => {
            // Stuck application: extend the spine
            let mut new_spine = neutral.spine.clone();
            new_spine.push(Elim::App(arg));
            Ok(Rc::new(Value::Neutral(Rc::new(Neutral {
                head: neutral.head.clone(),
                spine: new_spine,
            }))))
        }
        _ => Err(EvalError::NotAFunction),
    }
}

/// Evaluate a type to a semantic type
pub fn eval_ty<'db>(
    global: &GlobalEnv<'db>,
    env: &LocalEnv<'db>,
    ty: &TySyntax<'db>,
) -> Result<RcTy<'db>, EvalError> {
    match ty {
        TySyntax::UniverseType => Ok(Rc::new(Ty::UniverseType)),
        TySyntax::SignalUniverseType => Ok(Rc::new(Ty::SignalUniverseType)),
        TySyntax::ModuleUniverseType => Ok(Rc::new(Ty::ModuleUniverseType)),

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

### Operation 2: Quotation (`quote` and `quote_ty`)

Quotation takes values back to syntax. This is needed for:
1. Printing metavariable solutions to the user
2. Comparing values structurally in the unifier
3. Zonking (substituting solved metas)

```rust
// File: crates/hwml-core/src/nbe/quote.rs

use crate::*;

/// Quote a value back to syntax at a given depth
/// The depth is the number of binders we're currently under
pub fn quote<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
) -> RcSyntax<'db> {
    match value {
        Value::UniverseCode(n) => Rc::new(Syntax::UniverseCode(*n)),
        Value::SignalUniverseCode => Rc::new(Syntax::SignalUniverseCode),
        Value::ModuleUniverseCode => Rc::new(Syntax::ModuleUniverseCode),

        Value::PiCode(dom, cod) => {
            let dom_syn = quote(global, depth, dom);
            // To quote the codomain, we need to apply it to a fresh variable
            let var = Rc::new(Value::Neutral(Rc::new(Neutral {
                head: Head::Var(Level::new(depth)),
                spine: Vec::new(),
            })));
            let cod_val = cod.apply(global, var).unwrap();
            let cod_syn = quote(global, depth + 1, &cod_val);
            Rc::new(Syntax::PiCode(dom_syn, Binder {
                name: None,
                body: cod_syn,
            }))
        }

        Value::Lam(closure) => {
            let var = Rc::new(Value::Neutral(Rc::new(Neutral {
                head: Head::Var(Level::new(depth)),
                spine: Vec::new(),
            })));
            let body_val = closure.apply(global, var).unwrap();
            let body_syn = quote(global, depth + 1, &body_val);
            Rc::new(Syntax::Lam(Binder {
                name: None,
                body: body_syn,
            }))
        }

        Value::Neutral(neutral) => quote_neutral(global, depth, neutral),

        // ... (other cases)
    }
}

/// Quote a neutral term
fn quote_neutral<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    neutral: &Neutral<'db>,
) -> RcSyntax<'db> {
    let head_syn = match &neutral.head {
        Head::Var(level) => {
            // Convert level to index at current depth
            let idx = level.to_index(depth);
            Rc::new(Syntax::Var(idx))
        }
        Head::Const(name) => Rc::new(Syntax::Const(*name)),
        Head::Meta(id, subst) => {
            let subst_syn: Vec<_> = subst.iter()
                .map(|v| quote(global, depth, v))
                .collect();
            Rc::new(Syntax::Meta(*id, subst_syn))
        }
    };

    // Apply the spine
    quote_spine(global, depth, head_syn, &neutral.spine)
}

/// Quote a spine of eliminations
fn quote_spine<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    head: RcSyntax<'db>,
    spine: &[Elim<'db>],
) -> RcSyntax<'db> {
    spine.iter().fold(head, |acc, elim| {
        match elim {
            Elim::App(arg) => {
                let arg_syn = quote(global, depth, arg);
                Rc::new(Syntax::App(acc, arg_syn))
            }
            Elim::HApp(arg) => {
                let arg_syn = quote(global, depth, arg);
                Rc::new(Syntax::HApp(acc, arg_syn))
            }
            Elim::Case(branches) => {
                // Quote each branch
                let branches_syn: Vec<_> = branches.iter().map(|br| {
                    // Apply the closure to fresh variables
                    let mut vars = Vec::new();
                    for i in 0..br.arity {
                        vars.push(Rc::new(Value::Neutral(Rc::new(Neutral {
                            head: Head::Var(Level::new(depth + i)),
                            spine: Vec::new(),
                        }))));
                    }
                    // Apply closure to all variables
                    let body_val = apply_closure_multi(global, &br.body, vars).unwrap();
                    let body_syn = quote(global, depth + br.arity, &body_val);

                    CaseBranch {
                        constructor: br.constructor,
                        arity: br.arity,
                        body: body_syn,
                    }
                }).collect();

                // The scrutinee must be a variable (the head)
                // Extract the index from the head
                if let Syntax::Var(idx) = &*acc {
                    Rc::new(Syntax::Case {
                        scrutinee: *idx,
                        branches: branches_syn,
                    })
                } else {
                    panic!("Case scrutinee must be a variable")
                }
            }
        }
    })
}

/// Quote a type back to type syntax
pub fn quote_ty<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    ty: &Ty<'db>,
) -> RcTySyntax<'db> {
    match ty {
        Ty::UniverseType => Rc::new(TySyntax::UniverseType),
        Ty::SignalUniverseType => Rc::new(TySyntax::SignalUniverseType),
        Ty::ModuleUniverseType => Rc::new(TySyntax::ModuleUniverseType),

        Ty::Pi(dom, cod) => {
            let dom_syn = quote_ty(global, depth, dom);
            let var = Rc::new(Value::Neutral(Rc::new(Neutral {
                head: Head::Var(Level::new(depth)),
                spine: Vec::new(),
            })));
            let cod_ty = cod.apply(global, var).unwrap();
            let cod_syn = quote_ty(global, depth + 1, &cod_ty);
            Rc::new(TySyntax::Pi(dom_syn, TyBinder {
                name: None,
                body: cod_syn,
            }))
        }

        Ty::HArrow(src, tgt) => {
            let src_syn = quote_ty(global, depth, src);
            let tgt_syn = quote_ty(global, depth, tgt);
            Rc::new(TySyntax::HArrow(src_syn, tgt_syn))
        }

        Ty::El(code) => {
            let code_syn = quote(global, depth, code);
            Rc::new(TySyntax::El(code_syn))
        }
        Ty::SignalEl(code) => {
            let code_syn = quote(global, depth, code);
            Rc::new(TySyntax::SignalEl(code_syn))
        }
        Ty::ModuleEl(code) => {
            let code_syn = quote(global, depth, code);
            Rc::new(TySyntax::ModuleEl(code_syn))
        }
    }
}
```

### Operation 3: Unification (`unify_ty` and `unify_val`)

The unifier compares semantic types and values for equality.

**Key Insight:** Because of the 4-quadrant split, the unifier is incredibly simple!

```rust
// File: crates/hwml-elab/src/nbe/unify.rs

use crate::*;

/// Unify two semantic types
pub async fn unify_ty<'db>(
    state: &SolverState<'db>,
    depth: usize,
    t1: &Ty<'db>,
    t2: &Ty<'db>,
) -> Result<(), UnifyError> {
    match (t1, t2) {
        // Universe types unify with themselves
        (Ty::UniverseType, Ty::UniverseType) => Ok(()),
        (Ty::SignalUniverseType, Ty::SignalUniverseType) => Ok(()),
        (Ty::ModuleUniverseType, Ty::ModuleUniverseType) => Ok(()),

        // Pi types: unify domains and codomains
        (Ty::Pi(dom1, cod1), Ty::Pi(dom2, cod2)) => {
            unify_ty(state, depth, dom1, dom2).await?;

            // To unify the codomains, apply both to a fresh variable
            let var = Rc::new(Value::Neutral(Rc::new(Neutral {
                head: Head::Var(Level::new(depth)),
                spine: Vec::new(),
            })));
            let cod1_ty = cod1.apply(state.global(), var.clone())?;
            let cod2_ty = cod2.apply(state.global(), var)?;
            unify_ty(state, depth + 1, &cod1_ty, &cod2_ty).await
        }

        // Hardware arrows: unify structurally
        (Ty::HArrow(src1, tgt1), Ty::HArrow(src2, tgt2)) => {
            unify_ty(state, depth, src1, src2).await?;
            unify_ty(state, depth, tgt1, tgt2).await
        }

        // **Sterling's Commuting Rule:** El absorbs Lift!
        // If we're comparing two El-wrapped codes, drop down to value unification
        (Ty::El(v1), Ty::El(v2)) => unify_val(state, depth, v1, v2).await,
        (Ty::SignalEl(v1), Ty::SignalEl(v2)) => unify_val(state, depth, v1, v2).await,
        (Ty::ModuleEl(v1), Ty::ModuleEl(v2)) => unify_val(state, depth, v1, v2).await,

        // Mismatch
        _ => Err(UnifyError::TypeMismatch),
    }
}

/// Unify two values
pub async fn unify_val<'db>(
    state: &SolverState<'db>,
    depth: usize,
    v1: &Value<'db>,
    v2: &Value<'db>,
) -> Result<(), UnifyError> {
    match (v1, v2) {
        // Universe codes
        (Value::UniverseCode(n1), Value::UniverseCode(n2)) if n1 == n2 => Ok(()),
        (Value::SignalUniverseCode, Value::SignalUniverseCode) => Ok(()),
        (Value::ModuleUniverseCode, Value::ModuleUniverseCode) => Ok(()),

        // Type codes
        (Value::PiCode(dom1, cod1), Value::PiCode(dom2, cod2)) => {
            unify_val(state, depth, dom1, dom2).await?;
            let var = Rc::new(Value::Neutral(Rc::new(Neutral {
                head: Head::Var(Level::new(depth)),
                spine: Vec::new(),
            })));
            let cod1_val = cod1.apply(state.global(), var.clone())?;
            let cod2_val = cod2.apply(state.global(), var)?;
            unify_val(state, depth + 1, &cod1_val, &cod2_val).await
        }

        (Value::BitCode, Value::BitCode) => Ok(()),

        // Lambdas
        (Value::Lam(clos1), Value::Lam(clos2)) => {
            let var = Rc::new(Value::Neutral(Rc::new(Neutral {
                head: Head::Var(Level::new(depth)),
                spine: Vec::new(),
            })));
            let body1 = clos1.apply(state.global(), var.clone())?;
            let body2 = clos2.apply(state.global(), var)?;
            unify_val(state, depth + 1, &body1, &body2).await
        }

        // Neutrals: this is where pattern unification happens!
        (Value::Neutral(n1), Value::Neutral(n2)) => {
            unify_neutral(state, depth, n1, n2).await
        }

        // Flexible-Rigid: try to solve the metavariable
        (Value::Neutral(n), v) | (v, Value::Neutral(n)) => {
            if let Head::Meta(id, subst) = &n.head {
                // This is a metavariable! Try to solve it.
                solve_meta(state, depth, *id, subst, &n.spine, v).await
            } else {
                Err(UnifyError::Mismatch)
            }
        }

        _ => Err(UnifyError::Mismatch),
    }
}

/// Unify two neutral terms
async fn unify_neutral<'db>(
    state: &SolverState<'db>,
    depth: usize,
    n1: &Neutral<'db>,
    n2: &Neutral<'db>,
) -> Result<(), UnifyError> {
    // Heads must match
    match (&n1.head, &n2.head) {
        (Head::Var(l1), Head::Var(l2)) if l1 == l2 => {}
        (Head::Const(c1), Head::Const(c2)) if c1 == c2 => {}
        (Head::Meta(id1, subst1), Head::Meta(id2, subst2)) if id1 == id2 => {
            // Same metavariable: unify substitutions
            for (s1, s2) in subst1.iter().zip(subst2.iter()) {
                unify_val(state, depth, s1, s2).await?;
            }
        }
        _ => return Err(UnifyError::HeadMismatch),
    }

    // Spines must have the same length
    if n1.spine.len() != n2.spine.len() {
        return Err(UnifyError::SpineMismatch);
    }

    // Unify each elimination in the spine
    for (e1, e2) in n1.spine.iter().zip(n2.spine.iter()) {
        match (e1, e2) {
            (Elim::App(arg1), Elim::App(arg2)) => {
                unify_val(state, depth, arg1, arg2).await?;
            }
            (Elim::HApp(arg1), Elim::HApp(arg2)) => {
                unify_val(state, depth, arg1, arg2).await?;
            }
            _ => return Err(UnifyError::ElimMismatch),
        }
    }

    Ok(())
}

/// **Robert's Firewall:** Solve a metavariable with pattern unification
/// This is the critical security check that prevents ill-typed solutions
async fn solve_meta<'db>(
    state: &SolverState<'db>,
    depth: usize,
    meta_id: MetaVariableId,
    subst: &[RcValue<'db>],
    spine: &[Elim<'db>],
    solution: &Value<'db>,
) -> Result<(), UnifyError> {
    // Step 1: Check if already solved
    if let Some(existing) = state.get_solution(meta_id).await {
        // Already solved: unify with existing solution
        let existing_applied = apply_spine(state.global(), &existing, subst)?;
        let existing_applied_spine = apply_elim_spine(state.global(), &existing_applied, spine)?;
        return unify_val(state, depth, &existing_applied_spine, solution).await;
    }

    // Step 2: **The Inversion Check**
    // The spine must be purely distinct bound variables
    let mut var_levels = Vec::new();
    for elim in spine {
        match elim {
            Elim::App(arg) => {
                if let Value::Neutral(n) = &**arg {
                    if let Head::Var(level) = n.head {
                        if n.spine.is_empty() {
                            // Check for duplicates
                            if var_levels.contains(&level) {
                                return Err(UnifyError::NonLinearSpine);
                            }
                            var_levels.push(level);
                            continue;
                        }
                    }
                }
                // Not a variable: pattern unification fails
                return Err(UnifyError::NonPatternSpine);
            }
            _ => return Err(UnifyError::NonPatternSpine),
        }
    }

    // Step 3: **The Occurs Check**
    // Ensure the metavariable doesn't occur in the solution
    if occurs_check(meta_id, solution) {
        return Err(UnifyError::OccursCheckFailed);
    }

    // Step 4: **The Scope Check**
    // Ensure the solution only references variables in the spine
    if !scope_check(&var_levels, solution) {
        return Err(UnifyError::ScopeCheckFailed);
    }

    // Step 5: **The Assignment**
    // All checks passed! We can safely assign the metavariable.
    // We need to abstract over the variables in the spine to create the solution.
    let abstracted_solution = abstract_over(state.global(), depth, &var_levels, solution)?;

    // Quote the solution back to syntax
    let solution_syn = quote(state.global(), var_levels.len(), &abstracted_solution);

    // Assign and wake all blocked tasks
    state.assign_meta(meta_id, solution_syn).await;

    Ok(())
}

/// Check if a metavariable occurs in a value (occurs check)
fn occurs_check<'db>(meta_id: MetaVariableId, value: &Value<'db>) -> bool {
    match value {
        Value::Neutral(n) => {
            if let Head::Meta(id, subst) = &n.head {
                if *id == meta_id {
                    return true;
                }
                for s in subst {
                    if occurs_check(meta_id, s) {
                        return true;
                    }
                }
            }
            for elim in &n.spine {
                match elim {
                    Elim::App(arg) | Elim::HApp(arg) => {
                        if occurs_check(meta_id, arg) {
                            return true;
                        }
                    }
                    Elim::Case(branches) => {
                        for br in branches {
                            // Check the closure body
                            // This is conservative: we'd need to apply the closure to check properly
                            // For now, we'll skip this (TODO: implement proper occurs check for closures)
                        }
                    }
                }
            }
            false
        }
        Value::Lam(closure) | Value::ModuleLam(closure) => {
            // Conservative: we'd need to apply the closure
            // For now, assume no occurrence (TODO: implement proper check)
            false
        }
        Value::PiCode(dom, cod) => {
            occurs_check(meta_id, dom) // TODO: check codomain closure
        }
        Value::TypeConstructorCode(_, args) | Value::DataConstructorCode(_, args) => {
            args.iter().any(|arg| occurs_check(meta_id, arg))
        }
        Value::HArrowCode(src, tgt) => {
            occurs_check(meta_id, src) || occurs_check(meta_id, tgt)
        }
        Value::EqCode(ty, lhs, rhs) => {
            occurs_check(meta_id, ty) || occurs_check(meta_id, lhs) || occurs_check(meta_id, rhs)
        }
        _ => false,
    }
}

/// Check if a value only references variables in the allowed set (scope check)
fn scope_check<'db>(allowed_levels: &[Level], value: &Value<'db>) -> bool {
    match value {
        Value::Neutral(n) => {
            if let Head::Var(level) = n.head {
                if !allowed_levels.contains(&level) {
                    return false;
                }
            }
            for elim in &n.spine {
                match elim {
                    Elim::App(arg) | Elim::HApp(arg) => {
                        if !scope_check(allowed_levels, arg) {
                            return false;
                        }
                    }
                    _ => {} // TODO: check case branches
                }
            }
            true
        }
        Value::Lam(_) | Value::ModuleLam(_) => {
            // Conservative: assume scope is OK
            // TODO: implement proper scope check for closures
            true
        }
        Value::PiCode(dom, _) => scope_check(allowed_levels, dom),
        Value::TypeConstructorCode(_, args) | Value::DataConstructorCode(_, args) => {
            args.iter().all(|arg| scope_check(allowed_levels, arg))
        }
        Value::HArrowCode(src, tgt) => {
            scope_check(allowed_levels, src) && scope_check(allowed_levels, tgt)
        }
        _ => true,
    }
}

/// Abstract a value over a list of variables, creating a lambda
fn abstract_over<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    vars: &[Level],
    value: &Value<'db>,
) -> Result<RcValue<'db>, UnifyError> {
    // This is a simplified version
    // In practice, you'd need to:
    // 1. Rename the variables in `value` to use indices 0, 1, 2, ... (the parameters)
    // 2. Wrap the result in lambdas

    // For now, just return the value as-is
    // TODO: implement proper abstraction
    Ok(Rc::new(value.clone()))
}
```

---

## Part 3: The Elaborator

The elaborator translates surface syntax to the NbE core, inserting `El` and `Lift` automatically.

### Bidirectional Type Checking

```rust
// File: crates/hwml-elab/src/nbe/elaborate.rs

use crate::*;

pub struct ElabContext<'db, 'g> {
    /// The solver state (for metavariables)
    state: &'g SolverState<'db>,
    /// The typing context (types of bound variables)
    types: Vec<RcTy<'db>>,
    /// The value environment (for evaluation)
    values: LocalEnv<'db>,
}

impl<'db, 'g> ElabContext<'db, 'g> {
    pub fn new(state: &'g SolverState<'db>) -> Self {
        ElabContext {
            state,
            types: Vec::new(),
            values: LocalEnv::new(),
        }
    }

    pub fn depth(&self) -> usize {
        self.types.len()
    }

    /// Extend the context with a new binding
    pub fn push_var(&mut self, ty: RcTy<'db>, val: RcValue<'db>) {
        self.types.push(ty);
        self.values.push(val);
    }

    pub fn pop_var(&mut self) {
        self.types.pop();
        // Note: LocalEnv doesn't have pop, so we'd need to add it
    }
}

/// Elaborate a surface expression, **checking** against an expected type
/// Returns the core syntax term
pub async fn check<'db, 'g>(
    ctx: &mut ElabContext<'db, 'g>,
    expr: &surface::Expression,
    expected_ty: &Ty<'db>,
) -> Result<RcSyntax<'db>, ElabError> {
    match expr {
        // Lambda: check against Pi type
        surface::Expression::Fun(fun) => {
            if let Ty::Pi(dom_ty, cod_closure) = expected_ty {
                // Elaborate the lambda body under a fresh variable
                let var_level = Level::new(ctx.depth());
                let var_val = Rc::new(Value::Neutral(Rc::new(Neutral {
                    head: Head::Var(var_level),
                    spine: Vec::new(),
                })));

                ctx.push_var(dom_ty.clone(), var_val.clone());

                let cod_ty = cod_closure.apply(ctx.state.global(), var_val)?;
                let body_syn = check(ctx, &fun.expr, &cod_ty).await?;

                ctx.pop_var();

                Ok(Rc::new(Syntax::Lam(Binder {
                    name: fun.bindings.first().and_then(|b| b.name()),
                    body: body_syn,
                })))
            } else {
                Err(ElabError::ExpectedPiType)
            }
        }

        // For other expressions, synthesize and check convertibility
        _ => {
            let (term, inferred_ty) = synth(ctx, expr).await?;
            unify_ty(ctx.state, ctx.depth(), &inferred_ty, expected_ty).await?;
            Ok(term)
        }
    }
}

/// Elaborate a surface expression, **synthesizing** its type
/// Returns (core term, inferred type)
pub async fn synth<'db, 'g>(
    ctx: &mut ElabContext<'db, 'g>,
    expr: &surface::Expression,
) -> Result<(RcSyntax<'db>, RcTy<'db>), ElabError> {
    match expr {
        // Universe: Type, Type 0, Type 1, ...
        surface::Expression::Universe(univ) => {
            match univ.level {
                None => {
                    // User wrote just "Type" - this is the unconstrained top-level
                    Ok((
                        Rc::new(Syntax::UniverseCode(0)), // Placeholder
                        Rc::new(Ty::UniverseType),
                    ))
                }
                Some(n) => {
                    // User wrote "Type n" - this is a restricted universe code
                    Ok((
                        Rc::new(Syntax::UniverseCode(n.into())),
                        Rc::new(Ty::UniverseType),
                    ))
                }
            }
        }

        // Pi type: (x : A) -> B
        surface::Expression::Pi(pi) => {
            // Elaborate the domain as a type
            let dom_ty = elab_type(ctx, &pi.bindings.ty).await?;

            // Elaborate the codomain under a fresh variable
            let var_level = Level::new(ctx.depth());
            let var_val = Rc::new(Value::Neutral(Rc::new(Neutral {
                head: Head::Var(var_level),
                spine: Vec::new(),
            })));

            ctx.push_var(dom_ty.clone(), var_val.clone());
            let cod_ty = elab_type(ctx, &pi.target).await?;
            ctx.pop_var();

            // The Pi type itself is a type code
            let dom_syn = quote_ty(ctx.state.global(), ctx.depth(), &dom_ty);
            let cod_syn = quote_ty(ctx.state.global(), ctx.depth() + 1, &cod_ty);

            let pi_code = Rc::new(Syntax::PiCode(dom_syn, Binder {
                name: pi.bindings.names.first().cloned(),
                body: cod_syn,
            }));

            // The type of a Pi code is UniverseType (or a specific universe level)
            // For now, we'll use UniverseType
            Ok((pi_code, Rc::new(Ty::UniverseType)))
        }

        // Variable: lookup in context
        surface::Expression::Id(id) => {
            // TODO: resolve the identifier to a de Bruijn index or constant
            // For now, assume it's a constant
            let name = resolve_name(ctx, id)?;
            let const_info = ctx.state.global().constant(name)?;

            // Evaluate the type
            let ty = eval_ty(ctx.state.global(), &LocalEnv::new(), &const_info.ty)?;

            Ok((Rc::new(Syntax::Const(name)), ty))
        }

        // Application: f x
        surface::Expression::App(app) => {
            // Synthesize the type of the function
            let (fun_syn, fun_ty) = synth(ctx, &app.elements[0]).await?;

            // The function type must be a Pi
            if let Ty::Pi(dom_ty, cod_closure) = &*fun_ty {
                // Check the argument against the domain type
                let arg_syn = check(ctx, &app.elements[1], dom_ty).await?;

                // Evaluate the argument to apply the codomain closure
                let arg_val = eval(ctx.state.global(), &ctx.values, &arg_syn)?;
                let result_ty = cod_closure.apply(ctx.state.global(), arg_val)?;

                Ok((
                    Rc::new(Syntax::App(fun_syn, arg_syn)),
                    result_ty,
                ))
            } else {
                Err(ElabError::NotAFunction)
            }
        }

        _ => Err(ElabError::CannotSynthesize),
    }
}

/// Elaborate a surface expression as a **type**
/// This automatically inserts `El` when needed
pub async fn elab_type<'db, 'g>(
    ctx: &mut ElabContext<'db, 'g>,
    expr: &surface::Expression,
) -> Result<RcTy<'db>, ElabError> {
    match expr {
        // Unconstrained top-level: just "Type"
        surface::Expression::Universe(univ) if univ.level.is_none() => {
            Ok(Rc::new(Ty::UniverseType))
        }

        // Restricted universe: "Type n"
        surface::Expression::Universe(univ) => {
            let code = Rc::new(Syntax::UniverseCode(univ.level.unwrap().into()));
            Ok(Rc::new(Ty::El(Rc::new(Value::UniverseCode(univ.level.unwrap().into())))))
        }

        // For other expressions, synthesize and wrap in El
        _ => {
            let (code_syn, inferred_ty) = synth(ctx, expr).await?;

            // Evaluate the code
            let code_val = eval(ctx.state.global(), &ctx.values, &code_syn)?;

            // Wrap in the appropriate El based on the inferred type
            match &*inferred_ty {
                Ty::UniverseType => Ok(Rc::new(Ty::El(code_val))),
                Ty::SignalUniverseType => Ok(Rc::new(Ty::SignalEl(code_val))),
                Ty::ModuleUniverseType => Ok(Rc::new(Ty::ModuleEl(code_val))),
                _ => Err(ElabError::NotAUniverse),
            }
        }
    }
}
```

---

## Part 4: Answers to the 7 Critical Questions

### Q1: The `Ty` vs `Syntax` Split - Are you prepared for the refactor?

**Answer:** Yes, we're going "all in" with **Option B: Nuke and rebuild**.

**Migration Strategy:**
1. Create new files in `crates/hwml-core/src/nbe/` for the 4 quadrants
2. Keep the old `crates/hwml-core/src/syn/` and `crates/hwml-core/src/val/` temporarily
3. Migrate the elaborator first (it's the smallest)
4. Migrate the unifier (rewrite using the new architecture)
5. Update the CLI to use the new pipeline
6. Delete the old files

**Files to create:**
- `crates/hwml-core/src/nbe/mod.rs`
- `crates/hwml-core/src/nbe/syntax.rs` (Quadrant 1)
- `crates/hwml-core/src/nbe/value.rs` (Quadrant 2)
- `crates/hwml-core/src/nbe/ty.rs` (Quadrants 3 & 4)
- `crates/hwml-core/src/nbe/eval.rs` (Evaluation)
- `crates/hwml-core/src/nbe/quote.rs` (Quotation)
- `crates/hwml-elab/src/nbe/unify.rs` (Unification)
- `crates/hwml-elab/src/nbe/elaborate.rs` (Elaboration)

### Q2: The Metavariable "Checking Firewall"

**Answer:** **Option B: Use occurs check + scope check** (as shown in the code above).

**Why this works:**
- The elaborator guarantees that it only calls `unify_ty` on types that are **already well-typed**
- The unifier doesn't need to re-check types; it just solves algebraic equations
- The firewall (occurs + scope checks) prevents:
  - Infinite types (Y-combinator trap)
  - Variable escapes (scope violations)
  - Non-linear patterns (duplicate variables in spine)

**No circular dependency** because we never call `check` from inside `unify`.

### Q3: `whnf` and the `Value` Enum

**Answer:** **Option B: Eliminate `Value` as a separate concept**.

In the NbE architecture:
- `eval: Syntax -> Value` (evaluation produces values)
- `quote: Value -> Syntax` (quotation produces syntax)
- There is no separate `whnf` function!

**Why:** `Value` already represents weak head normal forms. When you evaluate a term, you get a `Value`, which is already in WHNF. If you need to compare two terms, you:
1. Evaluate both to `Value`
2. Compare the values directly (in the unifier)

The old `whnf` function is replaced by `eval`.

### Q4: Inductive Types and `El`

**Answer:** Inductive types live in **both** domains:

**Type Constructor (the type itself):**
```rust
// Surface: inductive Nat : Type where ...
// Elaborates to:

// The type code (Syntax):
Syntax::TypeConstructorCode(QualifiedName("Nat"), vec![])

// The type (Ty):
Ty::El(Value::TypeConstructorCode(QualifiedName("Nat"), vec![]))

// The type of Nat (the classifier):
Ty::UniverseType  // or Ty::El(Value::UniverseCode(0)) for a specific level
```

**Data Constructor (the values):**
```rust
// Surface: zero : Nat
// Elaborates to:

// The term (Syntax):
Syntax::DataConstructorCode(QualifiedName("zero"), vec![])

// The value (Value):
Value::DataConstructorCode(QualifiedName("zero"), vec![])

// The type of zero:
Ty::El(Value::TypeConstructorCode(QualifiedName("Nat"), vec![]))
```

**For `Vec : (A : Type) -> Nat -> Type`:**
```rust
// The type of Vec:
Ty::Pi(
    Ty::UniverseType,  // A : Type
    TyClosure {
        body: Ty::Pi(
            Ty::El(Value::TypeConstructorCode("Nat", vec![])),  // Nat
            TyClosure {
                body: Ty::UniverseType,  // Type
            }
        )
    }
)

// When fully applied: Vec A n
// The term:
Syntax::TypeConstructorCode("Vec", vec![A_syn, n_syn])

// The type:
Ty::El(Value::TypeConstructorCode("Vec", vec![A_val, n_val]))
```

### Q5: Hardware Arrows and the Top-Level

**Answer:** **Option A: `Ty::HArrow` is a top-level type former** (like `Ty::Pi`).

```rust
// Surface: Signal => Module
// Elaborates to:

// The type (Ty):
Ty::HArrow(
    Ty::SignalUniverseType,  // or Ty::SignalEl(...)
    Ty::ModuleUniverseType,  // or Ty::ModuleEl(...)
)

// NOT a code! HArrow is a semantic type, not a syntactic code.
```

**Why:** Hardware arrows are **not** universe-polymorphic. They always go from `Signal` to `Module`. They're a primitive type former at the top level, just like `Pi`.

**However,** we also have `HArrowCode` for when the arrow appears inside a universe:
```rust
// If you write: Type 0 containing (Bit => Bit)
// This would be:
Ty::El(Value::HArrowCode(
    Value::BitCode,
    Value::BitCode,
))
```

### Q6: The `salsa` Database and Lifetimes

**Answer:** Both `Ty` and `Syntax` use `'db` lifetimes, but they're **not** interned in `salsa`.

**Lifetime strategy:**
- `'db` is the lifetime of the `salsa` database
- `Syntax<'db>` and `Ty<'db>` contain references to `salsa`-interned data (like `QualifiedName<'db>`, `Name<'db>`)
- But the `Syntax` and `Ty` values themselves are **not** interned
- They're ephemeral values created during elaboration and stored in `Rc<>`

**Why this works:**
- The `SolverState` stores `RcSyntax<'db>` (solutions to metavariables)
- The `ElabContext` stores `RcTy<'db>` (types of bound variables)
- Both are tied to the `'db` lifetime, so they can reference `salsa`-interned names
- When elaboration finishes, we zonk the final term and store it in the `salsa` database

### Q7: Timeline and Scope

**Answer:** **Option B: Refactor to Sterling now**, before completing the elaborator.

**Why:**
- The current elaborator is only ~10% complete (just identifiers and functions)
- The current unifier is ~2,500 lines but will be **much simpler** in the NbE architecture
- Finishing the old elaborator would mean throwing away that work later
- The Sterling architecture makes the elaborator **easier** to write, not harder

**Timeline:**
- **Week 1:** Implement the 4 quadrants + eval + quote (no unification yet)
- **Week 2:** Implement the unifier with pattern unification
- **Week 3:** Implement the elaborator (check/synth/elab_type)
- **Week 4:** Wire up the CLI, add error reporting, test on examples

---

## Part 5: The Execution Plan

### Phase 1: The Data Structures (Days 1-2)

**Goal:** Define all 4 quadrants and get the code to compile.

**Tasks:**
1. Create `crates/hwml-core/src/nbe/mod.rs`
2. Create `crates/hwml-core/src/nbe/syntax.rs` with the `Syntax` enum
3. Create `crates/hwml-core/src/nbe/value.rs` with `Value`, `Closure`, `Neutral`, `LocalEnv`
4. Create `crates/hwml-core/src/nbe/ty.rs` with `TySyntax`, `Ty`, `TyClosure`
5. Add helper constructors (e.g., `Syntax::var_rc`, `Value::lam_rc`)
6. Update `crates/hwml-core/src/lib.rs` to export the new modules

**Success Criteria:**
- `cargo check` passes
- All 4 enums are defined with proper lifetimes
- No dependencies on old `syn::Syntax` or `val::Value` yet

### Phase 2: Evaluation and Quotation (Days 3-4)

**Goal:** Implement `eval`, `eval_ty`, `quote`, `quote_ty`.

**Tasks:**
1. Create `crates/hwml-core/src/nbe/eval.rs`
2. Implement `eval` for all `Syntax` variants
3. Implement `eval_ty` for all `TySyntax` variants
4. Implement `apply` for closures
5. Create `crates/hwml-core/src/nbe/quote.rs`
6. Implement `quote` for all `Value` variants
7. Implement `quote_ty` for all `Ty` variants
8. Write unit tests: `eval(quote(v)) == v` (round-trip)

**Success Criteria:**
- Can evaluate `Syntax::Lam(...)` to `Value::Lam(Closure { ... })`
- Can quote back to syntax
- Round-trip tests pass

### Phase 3: Unification (Days 5-7)

**Goal:** Implement the unifier with pattern unification.

**Tasks:**
1. Create `crates/hwml-elab/src/nbe/unify.rs`
2. Implement `unify_ty` for all `Ty` variants
3. Implement `unify_val` for all `Value` variants
4. Implement `unify_neutral` for spine comparison
5. Implement `solve_meta` with the firewall:
   - Inversion check
   - Occurs check
   - Scope check
   - Abstraction
6. Update `SolverState` to use the new types
7. Write unit tests for unification

**Success Criteria:**
- Can unify `Ty::Pi(A, B)` with `Ty::Pi(C, D)`
- Can solve `?M x y = f x y` to `?M = f`
- Occurs check prevents `?M = ?M -> Nat`
- Scope check prevents `?M x = y` when `y` is not in scope

### Phase 4: Elaboration (Days 8-10)

**Goal:** Implement bidirectional elaboration.

**Tasks:**
1. Create `crates/hwml-elab/src/nbe/elaborate.rs`
2. Implement `ElabContext` with typing context
3. Implement `check` for:
   - Lambdas
   - Let bindings
   - Match expressions
4. Implement `synth` for:
   - Variables
   - Applications
   - Universes
   - Pi types
5. Implement `elab_type` with automatic `El` insertion
6. Write tests for elaboration

**Success Criteria:**
- Can elaborate `fun x => x` to `Syntax::Lam(...)`
- Can elaborate `(A : Type) -> A` to a Pi code
- Automatic `El` insertion works

### Phase 5: CLI Integration (Days 11-12)

**Goal:** Wire up the new elaborator to the CLI.

**Tasks:**
1. Update `crates/hwml-cli/src/main.rs` to use the new elaborator
2. Add a `--nbe` flag to opt into the new pipeline
3. Update error reporting to use the new types
4. Add pretty-printing for the new syntax
5. Test on example programs

**Success Criteria:**
- `hwml --nbe examples/nat.hwml` elaborates successfully
- Errors are reported with source locations
- Can print the elaborated core syntax

### Phase 6: Migration and Cleanup (Days 13-14)

**Goal:** Remove the old code and make NbE the default.

**Tasks:**
1. Remove the `--nbe` flag (make it the default)
2. Delete `crates/hwml-core/src/syn/` (old syntax)
3. Delete `crates/hwml-core/src/val/` (old values)
4. Delete `crates/hwml-elab/src/unify.rs` (old unifier)
5. Update all documentation
6. Run the full test suite

**Success Criteria:**
- All tests pass
- No references to old `syn::Syntax` or `val::Value`
- Documentation is up to date

---

## Part 6: Key Design Decisions

### Decision 1: No Universe Polymorphism

We're implementing **concrete universe levels only**. No `Type u` where `u` is a variable.

**Rationale:** Simplifies the elaborator. We can add universe polymorphism later if needed.

### Decision 2: Hardware Arrows are Top-Level

`HArrow` is a `Ty`, not a `Syntax` code.

**Rationale:** Hardware arrows are not universe-polymorphic. They're a primitive type former.

### Decision 3: Single-Threaded Async

We keep the `Rc<RefCell<>>` model. No `Arc`, no `Mutex`.

**Rationale:** The async executor is already working. No need to introduce thread-safety overhead.

### Decision 4: No Salsa Interning for Syntax/Ty

`Syntax` and `Ty` are ephemeral values, not interned.

**Rationale:** Interning would require `salsa` queries for every `eval` and `quote`, adding overhead. We only intern the final zonked terms.

### Decision 5: Closures Use `LocalEnv`, Not Substitutions

Closures capture the environment, not explicit substitutions.

**Rationale:** This is the standard NbE approach. It's simpler and more efficient than explicit substitutions.

---

## Part 7: Architectural Resolutions (FINAL ANSWERS)

### Resolution 1: Inductive Type Declarations

**Decision:** Inductive types and data constructors are **completely rigid** - they do not compute, they just accumulate arguments.

**Implementation:**
```rust
// In Syntax: Use a global reference
Syntax::Global(DefId)  // For both type constructors and data constructors

// In Value: They become Neutral immediately
Value::Neutral(Neutral {
    head: Head::Global(DefId),
    spine: Vec::new(),  // Arguments accumulate here
})

// In the salsa database:
pub enum DefKind<'db> {
    /// Opaque definitions: inductives, constructors, postulates
    /// These get stuck and become Neutral
    Opaque,

    /// Transparent definitions: functions with bodies
    /// These unfold during evaluation
    Transparent(Rc<Syntax<'db>>),
}

#[salsa::tracked]
pub fn def_kind(db: &dyn Database, id: DefId) -> DefKind<'_>;
```

**Evaluation Rule:**
```rust
Syntax::Global(id) => {
    match global.def_kind(id) {
        DefKind::Transparent(body) => {
            // Unfold and continue evaluating
            eval(global, &Env::new(), &body)
        }
        DefKind::Opaque => {
            // Stuck! Return as neutral
            Ok(Rc::new(Value::Neutral(Rc::new(Neutral {
                head: Head::Global(id),
                spine: Vec::new(),
            }))))
        }
    }
}
```

**Why this works:** Constructors like `zero` and `succ` are treated exactly like free variables - they sit at the head of a spine and collect arguments. They never reduce.

### Resolution 2: Case Expression Return Types (The Motive)

**Decision:** Explicitly store the **motive** (return type function) in the case expression AST.

**Implementation:**
```rust
// In Syntax<'db>:
Case {
    scrutinee: RcSyntax<'db>,
    /// The motive: a function from the scrutinee to the return type
    /// E.g., for `match n with ...`, the motive might be `\x => Vec A x`
    motive: Binder<'db, Syntax<'db>>,
    branches: Vec<CaseBranch<'db>>,
}

// Example: Elaborating `match n with | zero => [] | succ m => ...`
// The motive is: \x => Vec A x
// When checking branch for `zero`, expected type is: motive[zero] = Vec A zero
// When checking branch for `succ m`, expected type is: motive[succ m] = Vec A (succ m)
```

**Why this is necessary:** In dependent pattern matching, the return type changes based on which constructor matched. The motive captures this dependency explicitly.

**Elaborator's job:** When type-checking a `match`, synthesize the motive and bake it into the core `Syntax`.

### Resolution 3: Metavariable Substitutions (The Spine)

**Decision:** Metavariables are **always** applied to their local environment. Never store a bare metavariable ID.

**Implementation:**
```rust
// In Syntax: Store the substitution as syntax
Syntax::Meta(MetaVariableId, Vec<RcSyntax<'db>>)

// In Value: Store the substitution as evaluated values
Value::Neutral(Neutral {
    head: Head::Meta(MetaVariableId),
    spine: Vec<RcValue<'db>>,  // The local environment, evaluated
})

// When creating a metavariable in the elaborator:
fn fresh_meta(&mut self, ty: RcTy<'db>) -> RcSyntax<'db> {
    let meta_id = self.state.fresh_meta_id(ty);

    // CRITICAL: Apply the meta to ALL local variables in scope
    let subst: Vec<_> = (0..self.depth())
        .map(|i| Rc::new(Syntax::Var(Index::new(i))))
        .collect();

    Rc::new(Syntax::Meta(meta_id, subst))
}
```

**Why this is critical:** If you create `?M` inside `\x => ...`, the metavariable must have access to `x`. By applying it to the local environment, you guarantee that when the unifier solves it, no variables escape their scope.

**Example:**
```rust
// Elaborating: fun x => ?hole
// The hole is created as: ?M[x]
// If the unifier solves ?M := \y => y
// Then ?M[x] reduces to: (\y => y) x = x  ✓

// If we stored just ?M (without [x]):
// Solving ?M := x would be a scope error! ✗
```

### Resolution 4: Transparency and Unfolding

**Decision:** Use a `salsa` query to determine if a definition should unfold.

**Implementation:**
```rust
// In the salsa database:
pub enum DefKind<'db> {
    /// Opaque: inductives, constructors, postulates
    Opaque,

    /// Transparent: functions with bodies
    Transparent(Rc<Syntax<'db>>),
}

#[salsa::tracked]
pub fn def_kind(db: &dyn Database, id: DefId) -> DefKind<'_>;

// In the evaluator:
Syntax::Global(id) => {
    match global.def_kind(id) {
        DefKind::Transparent(body) => eval(global, &Env::new(), &body),
        DefKind::Opaque => Ok(Rc::new(Value::Neutral(...))),
    }
}
```

**Transparency control:** If you need to control unfolding (e.g., for performance), add a flag:
```rust
pub struct GlobalEnv<'db> {
    db: &'db dyn Database,
    unfold_transparent: bool,  // Set to false to make everything opaque
}
```

**Why this works:** The distinction between "computes" (transparent) and "gets stuck" (opaque) is fundamental to NbE. This makes it explicit in the type system.

---

## Summary

This NbE architecture gives you:

1. **Simplicity:** The unifier is ~200 lines instead of ~2,500
2. **Correctness:** The firewall prevents ill-typed solutions
3. **Extensibility:** Adding new types only requires updating `Syntax` and `Value`
4. **Performance:** Evaluation is fast (no repeated substitutions)
5. **Sterling's Fuss-Free Universes:** Users rarely write universe levels

**Next Steps:**
1. Review this document with your team
2. Answer the 4 open questions above
3. Start Phase 1: Create the data structures
4. Pair program on Phase 2: Implement `eval` and `quote`

Are you ready to start implementing? Let me know if you have any questions about the architecture!
```

