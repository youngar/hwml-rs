# System Context Report: HWML Elaborator Architecture

**Date:** 2026-03-12  
**Codebase:** `hwml-rust`  
**Purpose:** Architectural review for LCF-style Trusted Kernel transition

---

## 1. Salsa and Memory Management

### Database Definition

```rust
// crates/hwml-core/src/lib.rs
#[salsa::db]
pub trait Database: salsa::Database {}

#[salsa::db]
#[derive(Default)]
pub struct DatabaseImpl {
    storage: salsa::Storage<Self>,
}
```

### Lifetime Management

- **`'db` lifetime**: Tied to the Salsa database lifetime, pervasive throughout `Syntax<'db>` and `Value<'db>`
- **Memory model**: `Syntax` and `Value` nodes use **standard `Rc<T>` pointers** (not Salsa-interned, not arena-allocated)
- **Interning**: Only `SourceRange` and `QualifiedName` are Salsa-interned; AST nodes themselves are heap-allocated via `Rc`

### Key Implication
The `'db` lifetime is a **phantom lifetime** that ensures AST nodes don't outlive the database, but actual memory management is via reference counting.

---

## 2. The Current AST and Evaluation (NbE)

### Core Syntax Definition

```rust
// crates/hwml-core/src/syn/basic.rs (lines 78-116)
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub enum Syntax<'db> {
    // Type theory core
    Universe(Universe<'db>),
    Lift(Lift<'db>),
    Pi(Pi<'db>),
    Lambda(Lambda<'db>),
    Application(Application<'db>),
    Let(Let<'db>),
    
    // Inductive types
    TypeConstructor(TypeConstructor<'db>),
    DataConstructor(DataConstructor<'db>),
    Case(Case<'db>),
    
    // Equality
    Eq(EqType<'db>),
    Refl(Refl<'db>),
    Transport(Transport<'db>),
    Closure(Closure<'db>),
    
    // Hardware universes
    HardwareUniverse(HardwareUniverse<'db>),
    SLift(SLift<'db>),
    MLift(MLift<'db>),
    
    // Signal types
    SignalUniverse(SignalUniverse<'db>),
    Bit(Bit<'db>),
    Zero(Zero<'db>),
    One(One<'db>),
    
    // Module types
    ModuleUniverse(ModuleUniverse<'db>),
    HArrow(HArrow<'db>),
    Module(Module<'db>),
    HApplication(HApplication<'db>),
    
    // Variables and constants
    Prim(Prim<'db>),
    Constant(Constant<'db>),
    Variable(Variable<'db>),
    Metavariable(Metavariable<'db>),
    
    Check(Check<'db>),
}
```

### Semantic Domain (Value)

```rust
// crates/hwml-core/src/val.rs (lines 1-100, partial)
#[derive(Clone, Debug)]
pub enum Value<'db> {
    Universe(Universe<'db>),
    Lift(Lift<'db>),
    Pi(Pi<'db>),
    Lambda(Lambda<'db>),
    Let(Let<'db>),
    
    TypeConstructor(TypeConstructor<'db>),
    DataConstructor(DataConstructor<'db>),
    
    EqType(EqType<'db>),
    Refl(Refl<'db>),
    
    HardwareUniverse(HardwareUniverse<'db>),
    SLift(SLift<'db>),
    MLift(MLift<'db>),
    
    SignalUniverse(SignalUniverse<'db>),
    Bit(Bit<'db>),
    Zero(Zero<'db>),
    One(One<'db>),
    
    ModuleUniverse(ModuleUniverse<'db>),
    HArrow(HArrow<'db>),
    Module(Module<'db>),
    
    Prim(Prim<'db>),
    Constant(Constant<'db>),
    
    // Neutral terms (spine representation)
    Rigid(Rigid<'db>),  // Variables
    Flex(Flex<'db>),    // Metavariables
}
```

**Key structures:**
- `Closure<'db>`: Captures environment for lambda bodies and Pi targets
- `Flex<'db>`: Metavariable with spine of eliminators and local substitution
- `Rigid<'db>`: Variable with spine of eliminators

### NbE Functions

```rust
// crates/hwml-core/src/eval.rs (lines 83-86)
pub fn eval<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    stx: &Syntax<'db>,
) -> Result<RcValue<'db>, Error>

// crates/hwml-core/src/quote.rs (lines 62-67)
pub fn quote<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
    ty: &Value<'db>,
) -> Result<'db, RcSyntax<'db>>
```

**Interaction with SolverState:**
- `eval` does **not** interact with `SolverState` directly
- Metavariable solutions are propagated via `force()` before evaluation
- `quote` is type-directed and also does not touch `SolverState`

---

## 3. Current Elaboration and Unification Signatures

### Bidirectional Elaborator

```rust
// crates/hwml-elab/src/elaborator.rs (lines 522-527)
#[async_recursion::async_recursion(?Send)]
pub async fn check<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    expr: &surface::Expression,
    expected_ty: RcValue<'db>,
) -> RcSyntax<'db>

// crates/hwml-elab/src/elaborator.rs (lines 603-607)
#[async_recursion::async_recursion(?Send)]
pub async fn synth<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    expr: &surface::Expression,
) -> (RcSyntax<'db>, RcValue<'db>)
```

**Note:** `#[async_recursion(?Send)]` is required because `Rc` is not `Send` and we're single-threaded.

### Unification

```rust
// crates/hwml-elab/src/unify.rs (lines 914-920)
pub async fn unify<'db, 'g>(
    db: &'db dyn salsa::Database,
    ctx: SolverEnvironment<'db, 'g>,
    lhs: RcValue<'db>,
    rhs: RcValue<'db>,
    ty: RcValue<'db>,
) -> UnifyResult<'db>
```

### Blocking/Yielding Logic

When the elaborator encounters an unsolved metavariable that blocks progress:

```rust
// crates/hwml-elab/src/engine.rs (lines 700-719)
impl<'db, 'g> Future for WaitForResolved<'db, 'g> {
    type Output = RcSyntax<'db>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.ctx.poll_meta(self.meta, cx.waker(), self.reason.clone()) {
            Some(term) => Poll::Ready(term),
            None => Poll::Pending,  // ← Task yields here
        }
    }
}
```

**Flow:**
1. Task calls `.await` on `WaitForResolved`
2. `poll_meta` checks if metavariable is solved
3. If not solved, registers `Waker` and returns `Poll::Pending`
4. Executor suspends task until another task solves the meta and calls `waker.wake()`

---

## 4. The Executor (`engine.rs`)

### Core Data Structures

```rust
// crates/hwml-elab/src/engine.rs (lines 117-127)
struct MetaSlot<'db> {
    ty: RcValue<'db>,
    solution: Option<RcSyntax<'db>>,
    waiters: Vec<WaitingTask>,
    poisoned: bool,  // For error recovery
}

// crates/hwml-elab/src/engine.rs (lines 159-170)
pub struct SolverState<'db> {
    metas: HashMap<MetaVariableId, MetaSlot<'db>>,
    dependencies: HashMap<MetaVariableId, HashSet<MetaVariableId>>,
    next_meta_index: u16,
}

// crates/hwml-elab/src/common.rs (lines 269-272)
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MetaVariableId {
    pub local_index: u16,
}
```

### Fresh Meta Signature

```rust
// crates/hwml-elab/src/engine.rs (lines 185-193)
pub fn fresh_meta(&mut self, ty: RcValue<'db>) -> MetaVariableId {
    let local_index = self.next_meta_index;
    let id = MetaVariableId::new(local_index);
    self.next_meta_index += 1;
    self.metas.insert(id, MetaSlot::new(ty));
    id
}

// Wrapper that returns Flex value (lines 545-552)
pub fn fresh_meta(&self, ty: RcValue<'db>) -> RcValue<'db> {
    let id = self.fresh_meta_id(ty.clone());
    Rc::new(Value::metavariable(id, self.tc_env.values.local.clone(), ty))
}
```

### Executor Architecture

```rust
// crates/hwml-elab/src/engine.rs (lines 729-734)
struct TaskStorage<'db> {
    tasks: RefCell<Slab<Pin<Box<dyn Future<Output = Result<(), String>> + 'db>>>>,
    ready_queue: Rc<ReadyQueue>,
}

// crates/hwml-elab/src/engine.rs (lines 757-760)
pub struct SingleThreadedExecutor<'db> {
    storage: Rc<TaskStorage<'db>>,
}
```

**Queue Management:**
1. **Task spawning**: Tasks are inserted into a `Slab` (sparse array) and their ID is pushed to `ready_queue`
2. **Execution loop**: Executor pops task IDs from `ready_queue`, polls them via `Future::poll()`
3. **Waking**: When a metavariable is solved, all waiters' `Waker`s are called, re-enqueueing their task IDs
4. **Deadlock detection**: If `ready_queue` is empty but `tasks` slab is non-empty, report unsolved constraints

**Key insight:** Uses cooperative multitasking—tasks voluntarily yield when blocked on unsolved metas.

---

## 5. AST Construction Boundaries

### Current Construction Sites

**Primary constructor:** `crates/hwml-elab/src/elaborator.rs`
- The elaborator is the **only** module that constructs `Syntax<'db>` nodes during type checking
- Uses public constructors like `Syntax::lambda_rc()`, `Syntax::application_rc()`, etc.

**Other construction sites:**
1. **Parser** (`crates/hwml-core/src/syn/parse.rs`): Parses the **core syntax** directly (not surface syntax)
   - Used for testing and loading prelude definitions
   - Outputs `Syntax<'db>` directly

2. **Surface parser** (`crates/hwml-surface/src/`): Parses user code into `surface::Expression`
   - **Does NOT construct `Syntax<'db>`**
   - Outputs a separate surface AST that is elaborated by `elaborator.rs`

### Surface vs. Core AST

```rust
// crates/hwml-surface/src/syntax.rs (lines 39-52)
pub enum Expression {
    Pi(Pi),
    Arrow(Arrow),
    FatArrow(FatArrow),
    App(App),
    Fun(Fun),
    LetIn(LetIn),
    Match(Match),
    Underscore(Underscore),
    Paren(Paren),
    Num(Num),
    Str(Str),
    Id(Id),
}
```

**Separation:**
- Surface AST: User-facing syntax with syntactic sugar, no type information
- Core AST (`Syntax<'db>`): Fully elaborated, type-directed, de Bruijn indexed

### Feasibility of Making `Syntax` Constructors Private

**Easy:** Making constructors private to a `kernel` module is straightforward:
- Only `elaborator.rs` constructs `Syntax` during normal operation
- Parser is only used for testing/prelude loading (can be moved to `kernel` module)

**Challenge:** The parser currently constructs `Syntax` directly for testing. Would need to either:
1. Move parser into the trusted `kernel` module, or
2. Refactor tests to use the elaborator instead of direct parsing

---

## 6. Summary of Current Architecture

### Strengths ✅
- **Async constraint solving works**: Cooperative scheduling with `SingleThreadedExecutor`
- **Bidirectional elaboration complete**: `check` and `synth` fully implemented
- **Error recovery functional**: Poisoned metavariables prevent error cascades
- **NbE operational**: `eval` and `quote` handle full language
- **Separation of concerns**: Surface AST → Elaborator → Core AST is clean

### Gaps ⚠️
1. **No location tracking on metavariables**: When solver deadlocks, can't report WHERE the unsolved meta originated
2. **Universe level inference incomplete**: Hardcoded `UniverseLevel::new(0)` in many places
3. **Motive synthesis for dependent pattern matching**: Currently just `λz. expected_ty`, doesn't handle dependency
4. **No LCF-style kernel**: `Syntax` constructors are public, no guarantee of well-formedness by construction

### Architectural Readiness for LCF Transition
- **High**: The async infrastructure is complete and functional
- **Boundary is clear**: Only elaborator constructs `Syntax` (plus parser for testing)
- **Refactor scope**: ~2000 lines to wrap all `Syntax::*_rc()` calls in async kernel API
- **Not blocking**: Current architecture already validates everything through bidirectional typing

---

## 7. Recommended Next Steps

1. **SourceRange tracking** (~50 lines): Add `location: SourceRange` to `MetaSlot`, thread through `fresh_meta()` calls
2. **Universe level inference** (~100 lines): Replace hardcoded levels with proper inference
3. **Motive synthesis** (~150 lines): Implement dependency-aware motive generation for pattern matching
4. **(Optional) LCF kernel** (~2000 lines): Architectural improvement, not strictly necessary

---

**End of Report**

