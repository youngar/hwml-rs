# Async Unification Infrastructure Tutorial

This tutorial explains how the async infrastructure works in the surface-to-core elaborator, focusing on the unification engine in `crates/hwml-elab/src/unify.rs`.

## Overview

The elaborator uses a **cooperative async runtime** to solve unification constraints concurrently. When unification encounters an unsolved metavariable, it suspends (yields) and waits for that metavariable to be solved by another task. This enables constraint solving to make progress even when individual constraints are temporarily blocked.

## Core Components

### 1. The Solver State (`engine.rs`)

The `SolverState` is the central registry for all metavariables and their solutions:

```rust
pub struct SolverState<'db> {
    /// Vector of metavariable slots, indexed by MetaVariableId
    metas: Vec<MetaSlot<'db>>,
}

struct MetaSlot<'db> {
    ty: RcValue<'db>,              // Type of the metavariable
    solution: Option<RcSyntax<'db>>, // Solution (if solved)
    waiters: Vec<WaitingTask>,        // Tasks blocked on this meta
}
```

**Key operations:**
- `fresh_meta(ty)` - Allocate a new metavariable with the given type
- `poll_meta(meta, waker, reason)` - Try to read a solution; if unsolved, register the waker
- `solve(meta, value)` - Set the solution and wake all waiting tasks

### 2. The Executor (`engine.rs`)

The `SingleThreadedExecutor` is a lightweight cooperative scheduler:

```rust
pub struct SingleThreadedExecutor<'db> {
    storage: Rc<TaskStorage<'db>>,
}
```

It maintains a queue of runnable tasks and polls them in a loop. When a task returns `Poll::Pending`, it stays in the task storage until its waker is called.

**The execution loop:**
1. Pop a task from the ready queue
2. Create a waker for that task
3. Poll the task
4. If `Ready(Ok)` → remove task (success)
5. If `Ready(Err)` → abort with error
6. If `Pending` → leave in storage, wait for waker

### 3. Waiting on Metavariables (`engine.rs`)

`WaitForResolved` is a Future that blocks until a metavariable is solved:

```rust
pub struct WaitForResolved<'db, 'g> {
    ctx: SolverEnvironment<'db, 'g>,
    meta: MetaVariableId,
    reason: BlockReason,  // Why we're waiting (for error reporting)
}
```

When polled:
- If the meta is solved → return `Poll::Ready(solution)`
- If unsolved → register the waker and return `Poll::Pending`

When the meta is later solved via `ctx.solve()`, all registered wakers are called, resuming the waiting tasks.

## Async Unification Flow

### Example: Unifying Two Pi Types

```rust
async fn unify_pi<'db, 'g>(
    db: &'db dyn salsa::Database,
    mut ctx: SolverEnvironment<'db, 'g>,
    pi1: &Pi<'db>,
    pi2: &Pi<'db>,
    ty: RcValue<'db>,
) -> UnifyResult<'db> {
    // 1. Antiunify the domains (creates a fresh meta)
    let (source_fut, source) = antiunify(
        db, ctx.clone(),
        pi1.source.clone(),
        pi2.source.clone(),
        ty.clone(),
    );
    
    // 2. Extend context with the antiunified domain
    let var = ctx.tc_env.push_var(source);
    
    // 3. Apply closures to get codomains
    let lhs_target = run_closure(global, &pi1.target, [var.clone()])?;
    let rhs_target = run_closure(global, &pi2.target, [var])?;
    
    // 4. Unify codomains
    let target_fut = Box::pin(unify(db, ctx, lhs_target, rhs_target, ty));
    
    // 5. Await both futures concurrently
    let (source_result, target_result) = join!(source_fut, target_fut);
    source_result?;
    target_result
}
```

**Key points:**
- `antiunify` creates a fresh metavariable and spawns two unification tasks
- Both domain and codomain unifications run concurrently via `join!`
- If either encounters an unsolved meta, it suspends and yields to the executor

### Example: Forcing a Metavariable (`force.rs`)

Before unifying, we "force" values to substitute any solved metavariables:

```rust
pub fn force<'db, 'g>(
    ctx: &SolverEnvironment<'db, 'g>,
    mut value: RcValue<'db>,
) -> Result<RcValue<'db>, eval::Error> {
    while let Value::Flex(flex) = &*value {
        match ctx.solution(flex.head.id) {
            Some(syn_solution) => {
                // Meta is solved - substitute and continue
                let sem_solution = eval::substitute(global, &syn_solution, flex.head.local)?;
                value = eval::run_spine(global, sem_solution, &flex.spine)?;
            }
            None => break,  // Unsolved - stop forcing
        }
    }
    Ok(value)
}
```

This is **synchronous** - it only substitutes already-solved metas. If a meta is unsolved, forcing stops and returns the Flex value.

### Example: Waiting for a Solution (`unify.rs`)

The `whnf` function demonstrates async waiting:

```rust
async fn whnf<'db, 'g>(
    ctx: &SolverEnvironment<'db, 'g>,
    mut value: RcValue<'db>,
) -> Result<RcValue<'db>, UnificationError<'db>> {
    while let Value::Flex(flex) = &*value {
        // Wait for the meta to be solved (async!)
        let syn_solution = WaitForResolved::new(
            ctx.clone(),
            flex.head.id,
            BlockReason::generic("whnf")
        ).await;
        
        let sem_solution = eval::substitute(global, &syn_solution, flex.head.local)?;
        value = run_spine(global, sem_solution, &flex.spine)?;
    }
    Ok(value)
}
```

**Difference from `force`:**
- `force` is synchronous - returns immediately if meta is unsolved
- `whnf` is async - **waits** for the meta to be solved by another task

## Pattern Unification and Lowering

### Flex-Flex with Same Meta: Intersection

When unifying `?M[x, y] = ?M[x, z]`, we compute the intersection:

```rust
async fn unify_flex_same<'db, 'g>(...) -> UnifyResult<'db> {
    // Find positions where substitutions agree
    let mut intersection_indices = Vec::new();
    for i in 0..local1.depth() {
        if values_match_for_intersection(local1.get(i), local2.get(i)) {
            intersection_indices.push(i);
        }
    }
    
    // Create new meta that only depends on intersection
    let new_meta_id = ctx.fresh_meta_id(meta_ty);
    let solution = Syntax::metavariable_rc(new_meta_id, subst_vars);
    ctx.solve(flex.head.id, solution);
}
```

This restricts which variables the meta depends on.

### Flex with Non-Empty Spine: Lowering

When we have `?u[σ] @ a` (meta applied to arguments), we "lower" it:

```rust
async fn lower_flex<'db, 'g>(...) -> Result<RcValue<'db>, UnificationError<'db>> {
    // For ?u : Pi A B applied to argument a:
    // 1. Create fresh ?v : B
    // 2. Solve ?u := λx. ?v[σ', x]
    // 3. Return ?v[σ, a]
    
    let new_meta_id = ctx.fresh_meta_id(codomain_ty);
    let lambda_term = Syntax::lambda_rc(
        None,
        Syntax::metavariable_rc(new_meta_id, extended_subst)
    );
    ctx.solve(current_meta_id, lambda_term);
}
```

This transforms the problem into one where the meta has an empty spine.

## Rich Error Reporting

The `BlockReason` enum tracks **why** each task is waiting:

```rust
pub enum BlockReason {
    Generic(String),
    ExpectedShape(String),
    Unifying(String, String),
}
```

When the solver stalls (deadlock), it generates a blame report showing which metas are unsolved and why tasks are waiting on them.

## Summary

The async infrastructure enables:
1. **Concurrent constraint solving** - multiple unification tasks run in parallel
2. **Suspension on blocking** - tasks yield when they hit unsolved metas
3. **Automatic resumption** - solving a meta wakes all waiting tasks
4. **Rich error reporting** - track why each task is blocked

This design is inspired by Agda's constraint solver but uses Rust's async/await for cooperative scheduling.

