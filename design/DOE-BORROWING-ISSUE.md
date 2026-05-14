# DOE Postponed Check Borrowing Issue

**Status:** 🔴 Blocking DOE activation  
**Created:** 2026-05-13  
**Priority:** Medium (infrastructure complete, feature disabled)

---

## Executive Summary

The Dynamic Order Elaboration (DOE) infrastructure is fully implemented but currently disabled due to a Rust borrowing conflict. The core issue: `Solver` needs `&mut SolverState` to run, but to execute postponed checks, we need to create an `Elaborator`, which also requires `&mut SolverState`. Rust's borrow checker correctly prevents this double mutable borrow.

**Current State:**
- ✅ All DOE infrastructure in place (constraints, detection, blocking)
- ✅ All 542 tests passing
- 🔴 Postponing disabled with `if false` guard in `check_impl`
- 🔴 Placeholder resolution stubbed out in `step_postponed_check`

---

## The Problem in Detail

### Architecture Overview

The elaborator uses a constraint-based architecture with three key components:

```rust
pub struct Elaborator<'a, 'db> {
    pub kernel: Kernel<'a, 'db>,      // Typing rules + context
    pub context: ElabContext<'db>,    // Source tracking + backtrace
}

pub struct Kernel<'a, 'db> {
    pub global: &'a GlobalEnv<'db>,
    pub ctx: ElabCtx<'db>,             // Local variables (immutable snapshot)
    pub state: &'a mut SolverState<'db>,  // ← MUTABLE BORROW #1
    pub resolver: &'a Resolver<'db>,
    pub stub_table: &'a StubTable<'db>,
}

pub struct Solver<'a, 'db> {
    pub state: &'a mut SolverState<'db>,  // ← MUTABLE BORROW #2
    pub global: &'a GlobalEnv<'db>,
    pub db: &'db dyn salsa::Database,
}
```

### The Borrowing Conflict

When processing a `PostponedCheck` constraint, the solver needs to:

1. **Force the expected type** (resolve solved metas)
2. **Check if still meta-headed** → reblock if yes
3. **Run the postponed check** if the type is now concrete

Step 3 requires calling `expr::check()`, which has this signature:

```rust
pub fn check<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,  // ← Needs &mut SolverState inside!
    expr: &Expression,
    expected_ty: RcTy<'db>,
) -> Result<Checked<RcSyntax<'db>>, ElabError<'db>>
```

**The conflict:**

```rust
impl<'a, 'db> Solver<'a, 'db> {
    fn step_postponed_check(&mut self, ...) -> Result<...> {
        // self.state is &mut SolverState (BORROW #1 active)
        
        let forced_ty = force_ty(self.state, ...);  // OK, uses borrow #1
        
        // Now we need to create an Elaborator...
        let mut elab = Elaborator::new(
            global,
            captured_ctx,
            self.state,  // ❌ ERROR: cannot borrow as mutable more than once!
            resolver,
            stub_table,
            source,
        );
        
        // This would require a SECOND mutable borrow of self.state,
        // but we already have one active in the Solver!
    }
}
```

**Rust error:**
```
error[E0499]: cannot borrow `*self.state` as mutable more than once at a time
```

### Why This Happens

The `Solver::run()` loop looks like:

```rust
pub fn run(&mut self) -> Result<(), SolveError<'db>> {
    loop {
        let cid = self.state.pop_active()?;  // Using &mut self.state
        self.step_constraint(cid, ...)?;      // Still holds &mut self.state
    }
}
```

Inside `step_constraint`, we call `step_postponed_check`, which still has the mutable borrow active through `self`. There's no way to "pause" the solver, release the borrow, run elaboration, and resume.

---

## Current Workaround (Temporary)

The postponing logic is disabled:

```rust
// In elab/expr.rs::check_impl
if false {  // TODO(DOE): Disabled due to borrowing issue
    if let Some(meta_id) = is_meta_headed(&expected_ty) {
        // ... create placeholder and emit constraint ...
    }
}
```

The solver handler is stubbed:

```rust
// In solver.rs::step_postponed_check
fn step_postponed_check(&mut self, ...) -> Result<...> {
    // Force type, reblock if still meta-headed (this works)
    
    // TODO: Actually run the check (this doesn't work due to borrowing)
    self.state.mark_solved(cid);  // Just mark solved for now
    Ok(())
}
```

This means:
- ✅ Constraints are created and blocked correctly
- ✅ Wake-up graph works
- ❌ Postponed checks are never actually executed
- ❌ Placeholder metas remain unsolved

---

## Solution Options

### Option 1: Return Postponed Checks from Solver ⭐ (Recommended)

**Idea:** Solver identifies ready-to-run postponed checks but doesn't execute them. Instead, it returns them to the caller.

**Architecture:**

```rust
pub struct ReadyCheck<'db> {
    pub expr: Box<Expression>,
    pub expected_ty: RcTy<'db>,
    pub ctx: ElabCtx<'db>,
    pub placeholder: MetaId,
    pub depth: usize,
}

impl Solver {
    pub fn run(&mut self) -> Result<Vec<ReadyCheck<'db>>, SolveError<'db>> {
        let mut ready_checks = Vec::new();
        
        loop {
            let cid = match self.state.pop_active() { ... };
            
            match constraint {
                Constraint::PostponedCheck { ... } => {
                    if !is_meta_headed(&forced_ty) {
                        // Don't run here, just collect
                        ready_checks.push(ReadyCheck { ... });
                        self.state.mark_solved(cid);
                    } else {
                        // Still blocked, requeue
                        self.state.block_on(cid, &[meta_id]);
                    }
                }
                _ => { /* normal constraint handling */ }
            }
        }
        
        Ok(ready_checks)
    }
}
```

**Caller pattern:**

```rust
// In elab/decl.rs or program.rs
fn elaborate_with_doe<'a, 'db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
) -> Result<(), ElabError<'db>> {
    // ... elaborate definitions ...
    
    loop {
        // Run solver (no longer holds &mut state after this)
        let ready_checks = {
            let mut solver = Solver::new(elab.kernel.state, elab.kernel.global, db);
            solver.run()?
        };
        
        // Now elab can use &mut state again!
        for check in ready_checks {
            let result = expr::check_with_context(db, elab, &check)?;
            elab.kernel.state.solve_meta(
                check.placeholder,
                result.syntax,
                result.value,
            )?;
        }
        
        // If no checks were ready, we're done
        if ready_checks.is_empty() {
            break;
        }
    }
    
    Ok(())
}
```

**Pros:**
- ✅ Clean separation of concerns
- ✅ No borrowing conflicts
- ✅ Solver remains pure (no elaboration)
- ✅ Easy to test postponed checks separately

**Cons:**
- ⚠️ Changes solver API (minor breaking change)
- ⚠️ Caller needs to loop (solver → check → solver)

**Estimated effort:** ~200 lines, 2-3 hours

---

### Option 2: Interior Mutability with RefCell

**Idea:** Wrap `SolverState` in `Rc<RefCell<SolverState>>` to allow runtime-checked borrowing.

**Architecture:**

```rust
pub struct Kernel<'a, 'db> {
    pub global: &'a GlobalEnv<'db>,
    pub ctx: ElabCtx<'db>,
    pub state: &'a RefCell<SolverState<'db>>,  // ← Changed!
    // ...
}

impl Solver {
    fn step_postponed_check(&mut self, ...) -> Result<...> {
        // Temporarily release the borrow
        let forced_ty = {
            let state = self.state.borrow();
            force_ty(&state, ...)
        }; // Borrow released here

        if !is_meta_headed(&forced_ty) {
            // Create elaborator (gets new borrow)
            let mut elab = Elaborator::new(..., self.state, ...);
            let result = expr::check(db, &mut elab, ...)?;

            // Solve placeholder
            self.state.borrow_mut().solve_meta(...)?;
        }
        Ok(())
    }
}
```

**Pros:**
- ✅ No API changes
- ✅ Minimal code changes
- ✅ Solver can directly run elaboration

**Cons:**
- ❌ Runtime borrow checking (potential panics)
- ❌ Performance overhead (`RefCell` checks)
- ❌ Less explicit about borrowing discipline
- ❌ Panic risk if borrow rules violated at runtime

**Estimated effort:** ~150 lines, 1-2 hours

**Risk:** Medium (runtime panics possible)

---

### Option 3: Two-Phase Solver

**Idea:** Split constraint solving into two phases: (1) constraint resolution, (2) elaboration execution.

**Architecture:**

```rust
pub struct SolverPhase1Result<'db> {
    pub solved: Vec<ConstraintId>,
    pub blocked: Vec<ConstraintId>,
    pub ready_for_elab: Vec<ReadyCheck<'db>>,
}

impl Solver {
    // Phase 1: Pure constraint logic (no elaboration)
    pub fn resolve_constraints(&mut self) -> Result<SolverPhase1Result<'db>, ...> {
        // ... process Eq, LevelLeq, ResolveDot ...
        // ... collect PostponedChecks that are ready ...
    }
}

// Phase 2: Caller runs elaboration
fn elaborate_postponed_checks(
    ready: Vec<ReadyCheck<'db>>,
    elab: &mut Elaborator,
) -> Result<(), ...> {
    for check in ready {
        // ... run check, solve placeholder ...
    }
}
```

**Pros:**
- ✅ Clean phase separation
- ✅ Easier to reason about
- ✅ Better for debugging

**Cons:**
- ⚠️ More complex API
- ⚠️ Caller must coordinate phases

**Estimated effort:** ~250 lines, 3-4 hours

---

### Option 4: Separate Elaboration Queue

**Idea:** Postponed checks go into a separate queue, processed after main solver loop.

**Architecture:**

```rust
pub struct SolverState<'db> {
    // Existing fields...
    pub elab_queue: Vec<ReadyCheck<'db>>,  // NEW
}

impl Solver {
    fn step_postponed_check(&mut self, ...) -> Result<...> {
        if !is_meta_headed(&forced_ty) {
            // Don't elaborate here, queue it
            self.state.elab_queue.push(ReadyCheck { ... });
            self.state.mark_solved(cid);
        }
        Ok(())
    }
}

// In program elaborator:
fn run_solver_with_elab(db, elab) -> Result<()> {
    loop {
        {
            let mut solver = Solver::new(elab.kernel.state, ...);
            solver.run()?;
        } // Release solver borrow

        // Process elaboration queue
        let queue = std::mem::take(&mut elab.kernel.state.elab_queue);
        if queue.is_empty() { break; }

        for check in queue {
            // ... run check, solve placeholder ...
        }
    }
    Ok(())
}
```

**Pros:**
- ✅ Minimal API changes
- ✅ Queue in `SolverState` (natural home)
- ✅ Clear separation

**Cons:**
- ⚠️ Mutable state grows (`elab_queue` field)
- ⚠️ Caller must remember to drain queue

**Estimated effort:** ~180 lines, 2 hours

---

## Comparison Matrix

| Option | API Changes | Borrow Safety | Perf | Complexity | Risk |
|--------|-------------|---------------|------|------------|------|
| **1. Return from Solver** | Minor | Compile-time ✅ | Best | Low | Low |
| **2. RefCell** | None | Runtime ⚠️ | Overhead | Low | Medium |
| **3. Two-Phase** | Major | Compile-time ✅ | Best | Medium | Low |
| **4. Elab Queue** | Minor | Compile-time ✅ | Best | Low | Low |

---

## Recommendation

**Option 1: Return Postponed Checks from Solver** ⭐

**Rationale:**
1. **Compile-time safety:** No runtime borrow panics
2. **Clean design:** Solver focuses on constraint logic, caller handles elaboration
3. **Testable:** Easy to test solver and elaboration separately
4. **Minimal risk:** Small, focused API change

**Implementation Plan:**

1. **Define `ReadyCheck` struct** in `solver.rs` (~10 lines)
2. **Change `Solver::run()` return type** to `Result<Vec<ReadyCheck>, ...>` (~5 lines)
3. **Modify `step_postponed_check`** to collect instead of execute (~20 lines)
4. **Update all `Solver::run()` call sites** (~15 locations × 10 lines = ~150 lines)
5. **Add elaboration loop** in program/decl elaborators (~30 lines)
6. **Test with postponed checks** (~50 lines)

**Total:** ~265 lines, ~3 hours work

**Migration path:**
- Existing constraints (Eq, ResolveDot) unchanged
- Only PostponedCheck affected
- Can implement incrementally (return empty Vec first)

---

## Next Steps

1. **Review this design** with team/user
2. **Choose solution** (recommend Option 1)
3. **Implement** in focused session
4. **Enable DOE** by removing `if false` guard
5. **Test** with elaboration-zoo examples
6. **Celebrate** first-class polymorphism! 🎉

---

## References

- **Original research:** `wiki/research/implicit-arguments-first-class-polymorphism.md`
- **Implementation plan:** `IMPLICIT-ARGUMENTS-IMPLEMENTATION-PLAN-PART2.md`
- **Constraint infrastructure:** `crates/hwml-elab/src/constraint.rs`
- **Solver implementation:** `crates/hwml-elab/src/solver.rs`
- **Check implementation:** `crates/hwml-elab/src/elab/expr.rs`

---

## Appendix: Detailed Call Stack

To understand the borrowing issue, here's the full call stack when it occurs:

```
1. elab/decl.rs::elab_constant()
   └─ elab: &mut Elaborator<'a, 'db>
      └─ kernel.state: &'a mut SolverState<'db>

2. elab/decl.rs::run_solver()
   └─ Creates: Solver { state: &'a mut SolverState }
      └─ BORROW #1: Solver owns &mut SolverState

3. solver.rs::Solver::run()
   └─ loop {
        └─ self.step_constraint(cid, ...)
           └─ BORROW #1 STILL ACTIVE (self.state)

4. solver.rs::step_constraint()
   └─ match constraint {
        Constraint::PostponedCheck { ... } =>
          └─ self.step_postponed_check(...)
             └─ BORROW #1 STILL ACTIVE

5. solver.rs::step_postponed_check()
   └─ Need to call: expr::check(db, &mut elab, ...)
      └─ Need to create: Elaborator { state: &'a mut SolverState }
         └─ ❌ NEED BORROW #2, but BORROW #1 still active!
```

The lifetime `'a` of the Solver's borrow extends from step 2 all the way through step 5, preventing us from creating a new `&mut` borrow for the Elaborator.

**Key insight:** We can't "pause" the Solver's borrow. We must either:
- Exit the Solver before creating an Elaborator (Options 1, 3, 4)
- Use runtime borrow checking (Option 2)



