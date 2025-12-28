use slab::Slab;
use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

use hwml_core::common::MetaVariableId;
use hwml_core::syn::RcSyntax;

/// Information stored for each metavariable slot.
#[derive(Clone)]
struct MetaSlot<'db> {
    /// The solution for this metavariable, if solved
    solution: Option<RcSyntax<'db>>,
    /// Tasks waiting for this metavariable to be solved
    waiters: Vec<Waker>,
}

impl<'db> MetaSlot<'db> {
    fn new() -> Self {
        Self {
            solution: None,
            waiters: Vec::new(),
        }
    }

    fn is_solved(&self) -> bool {
        self.solution.is_some()
    }
}

/// The central state for the constraint solver. Contains solved metavariables
/// and wait lists for blocked tasks.
pub struct SolverState<'db> {
    /// Vector of metavariable slots, indexed by MetaVariableId
    /// Each slot contains the solution (if solved) and list of waiting tasks
    metas: Vec<MetaSlot<'db>>,
}

impl<'db> SolverState<'db> {
    pub fn new() -> Self {
        Self { metas: Vec::new() }
    }

    /// Allocate a fresh metavariable.
    ///
    /// This is the **only** way to create new MetaVariableIds for this solver.
    /// By allocating through the state, we ensure the vector is always properly sized.
    pub fn fresh_meta(&mut self) -> MetaVariableId {
        let id = MetaVariableId(self.metas.len());
        self.metas.push(MetaSlot::new());
        println!("[Solver] Allocated fresh meta {}", id);
        id
    }

    /// Attempt to read a meta. If solved, return the value. If not solved,
    /// register the waker and return None.
    fn poll_meta(&mut self, meta: MetaVariableId, waker: &Waker) -> Option<RcSyntax<'db>> {
        // Meta should already exist if it was allocated through fresh_meta
        assert!(
            meta.0 < self.metas.len(),
            "Meta {} not allocated! Use fresh_meta() to allocate metavariables.",
            meta
        );

        let slot = &mut self.metas[meta.0];

        match &slot.solution {
            Some(term) => Some(term.clone()),
            None => {
                // Register this task to be woken when the meta is solved
                slot.waiters.push(waker.clone());
                None
            }
        }
    }

    /// Get the solution for a specific metavariable, if it has been solved.
    pub fn get_solution(&self, meta: MetaVariableId) -> Option<RcSyntax<'db>> {
        if meta.0 < self.metas.len() {
            self.metas[meta.0].solution.clone()
        } else {
            None
        }
    }

    /// Get the final substitution as a vector indexed by MetaVariableId.
    ///
    /// Returns a Vec where `result[meta.0]` gives the solution for `meta`.
    /// Unsolved metas have `None` at their index.
    ///
    /// This is more efficient than a HashMap since MetaVariableIds are
    /// sequential integers, allowing O(1) lookup by direct indexing.
    pub fn get_substitution(&self) -> Vec<Option<RcSyntax<'db>>> {
        self.metas
            .iter()
            .map(|slot| slot.solution.clone())
            .collect()
    }
}

/// A shared handle to the solver state.
/// This is cloned and passed to all constraint futures.
#[derive(Clone)]
pub struct ContextHandle<'db>(Rc<RefCell<SolverState<'db>>>);

impl<'db> ContextHandle<'db> {
    /// Create a new context handle with empty state
    pub fn new() -> Self {
        ContextHandle(Rc::new(RefCell::new(SolverState::new())))
    }

    /// Attempt to read a meta. If solved, return value.
    /// If not, register the current Waker and return None.
    pub fn poll_meta(&self, meta: MetaVariableId, waker: &Waker) -> Option<RcSyntax<'db>> {
        self.0.borrow_mut().poll_meta(meta, waker)
    }

    /// Allocate a fresh metavariable.
    pub fn fresh_meta(&self) -> MetaVariableId {
        self.0.borrow_mut().fresh_meta()
    }

    /// Get the solution for a specific metavariable, if it has been solved.
    pub fn get_solution(&self, meta: MetaVariableId) -> Option<RcSyntax<'db>> {
        self.0.borrow().get_solution(meta)
    }

    /// Solve a meta and wake everyone up
    pub fn define_meta(&self, meta: MetaVariableId, value: RcSyntax<'db>) {
        // We need to be careful here to avoid holding the borrow when waking
        let wakers = {
            let mut state = self.0.borrow_mut();
            println!("[Solver] Defining {} := {:?}", meta, value);

            // Meta should already exist if it was allocated through fresh_meta
            assert!(
                meta.0 < state.metas.len(),
                "Meta {} not allocated! Use fresh_meta() to allocate metavariables.",
                meta
            );

            // Get the slot and set the solution
            let slot = &mut state.metas[meta.0];
            slot.solution = Some(value);

            // Take the waiters (leaving an empty vec)
            std::mem::take(&mut slot.waiters)
        };

        // Now wake without holding the borrow
        if !wakers.is_empty() {
            println!("[Solver] Waking {} tasks waiting on {}", wakers.len(), meta);
            for waker in wakers {
                waker.wake();
            }
        }
    }

    /// Get the final substitution as a vector indexed by MetaVariableId.
    ///
    /// Returns a Vec where `result[meta.0]` gives the solution for `meta`.
    /// Unsolved metas have `None` at their index.
    pub fn get_substitution(&self) -> Vec<Option<RcSyntax<'db>>> {
        self.0.borrow().get_substitution()
    }
}

/// A Future that blocks until a specific MetaVar is solved.
/// This replaces the `BlockOnMeta` constructor in Haskell.
pub struct WaitForResolved<'db> {
    ctx: ContextHandle<'db>,
    meta: MetaVariableId,
}

impl<'db> WaitForResolved<'db> {
    pub fn new(ctx: ContextHandle<'db>, meta: MetaVariableId) -> Self {
        WaitForResolved { ctx, meta }
    }
}

impl<'db> Future for WaitForResolved<'db> {
    type Output = RcSyntax<'db>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.ctx.poll_meta(self.meta, cx.waker()) {
            Some(term) => {
                println!("[WaitForResolved] Meta {} is resolved", self.meta);
                Poll::Ready(term)
            }
            None => {
                println!("[WaitForResolved] Blocked waiting on {}", self.meta);
                Poll::Pending
            }
        }
    }
}

type TaskId = usize;

/// The structure shared between the Executor and the Wakers.
/// Contains the queue of tasks that are ready to run.
struct ReadyQueue {
    queue: RefCell<VecDeque<TaskId>>,
}

/// A lightweight, single-threaded executor for constraint solving.
pub struct SingleThreadedExecutor<'db> {
    /// All spawned tasks, indexed by TaskId using a Slab allocator
    tasks: Slab<Pin<Box<dyn Future<Output = Result<(), String>> + 'db>>>,
    /// Queue of task IDs that are ready to run
    ready_queue: Rc<ReadyQueue>,
}

impl<'db> SingleThreadedExecutor<'db> {
    pub fn new() -> Self {
        Self {
            tasks: Slab::new(),
            ready_queue: Rc::new(ReadyQueue {
                queue: RefCell::new(VecDeque::new()),
            }),
        }
    }

    /// Spawn a new constraint task
    pub fn spawn<F>(&mut self, future: F)
    where
        F: Future<Output = Result<(), String>> + 'db,
    {
        // Slab automatically allocates the next available slot
        let id = self.tasks.insert(Box::pin(future));
        self.ready_queue.queue.borrow_mut().push_back(id);
        println!("[Executor] Spawned task {}", id);
    }

    /// The main loop. Runs until all tasks are done or stalled.
    /// Returns Ok if all tasks completed successfully.
    /// Returns Err if any task failed or if there's a deadlock.
    pub fn run(&mut self) -> Result<(), String> {
        println!("[Executor] Starting execution");

        loop {
            // Pop from the queue without holding the borrow
            let task_id = self.ready_queue.queue.borrow_mut().pop_front();

            let Some(task_id) = task_id else {
                break; // Queue is empty
            };

            let waker = self.create_waker(task_id);
            let mut context = Context::from_waker(&waker);

            // Use get_mut() to poll in-place - avoids remove/insert churn
            if let Some(task) = self.tasks.get_mut(task_id) {
                match task.as_mut().poll(&mut context) {
                    Poll::Ready(Ok(())) => {
                        println!("[Executor] Task {} finished successfully", task_id);
                        // Only remove when done - this frees the slot for reuse
                        let _ = self.tasks.remove(task_id);
                    }
                    Poll::Ready(Err(e)) => {
                        println!("[Executor] Task {} failed: {}", task_id, e);
                        let _ = self.tasks.remove(task_id);
                        return Err(format!("Task {} failed: {}", task_id, e));
                    }
                    Poll::Pending => {
                        println!("[Executor] Task {} is pending", task_id);
                        // Task stays in the slab - no remove/insert needed!
                        // It will be polled again when waker.wake() is called.
                    }
                }
            }
        }

        // Check for deadlock: if there are still pending tasks but the queue is empty
        if !self.tasks.is_empty() {
            let pending_tasks: Vec<_> = self.tasks.iter().map(|(id, _)| id).collect();
            return Err(format!(
                "Deadlock detected: {} tasks still pending but no progress can be made. Pending tasks: {:?}",
                self.tasks.len(),
                pending_tasks
            ));
        }

        println!("[Executor] All tasks completed successfully");
        Ok(())
    }

    // ========================================================================
    // WAKER IMPLEMENTATION
    // ========================================================================
    // The following methods implement the standard Rust waker pattern.
    // This is the same approach used by production executors, just adapted
    // for single-threaded use with Rc instead of Arc.
    //
    // The waker stores two pieces of data:
    // 1. The ReadyQueue (shared via Rc)
    // 2. The TaskId
    //
    // When wake() is called, it pushes the TaskId back onto the ReadyQueue.

    fn create_waker(&self, task_id: TaskId) -> Waker {
        let data = Box::new((self.ready_queue.clone(), task_id));
        let raw_data = Box::into_raw(data) as *const ();

        let vtable = &RawWakerVTable::new(
            Self::clone_waker,
            Self::wake,
            Self::wake_by_ref,
            Self::drop_waker,
        );

        let raw_waker = RawWaker::new(raw_data, vtable);
        unsafe { Waker::from_raw(raw_waker) }
    }

    unsafe fn clone_waker(data: *const ()) -> RawWaker {
        let data_box = data as *const (Rc<ReadyQueue>, TaskId);
        let (queue, task_id) = &*data_box;

        let new_data = Box::new((queue.clone(), *task_id));
        let new_raw_data = Box::into_raw(new_data) as *const ();

        RawWaker::new(
            new_raw_data,
            &RawWakerVTable::new(
                Self::clone_waker,
                Self::wake,
                Self::wake_by_ref,
                Self::drop_waker,
            ),
        )
    }

    unsafe fn wake(data: *const ()) {
        let data_box = Box::from_raw(data as *mut (Rc<ReadyQueue>, TaskId));
        let (queue, task_id) = *data_box;
        queue.queue.borrow_mut().push_back(task_id);
        println!("[Waker] Woke task {}", task_id);
    }

    unsafe fn wake_by_ref(data: *const ()) {
        let data_box = data as *const (Rc<ReadyQueue>, TaskId);
        let (queue, task_id) = &*data_box;
        queue.queue.borrow_mut().push_back(*task_id);
        println!("[Waker] Woke task {} (by ref)", task_id);
    }

    unsafe fn drop_waker(data: *const ()) {
        let _ = Box::from_raw(data as *mut (Rc<ReadyQueue>, TaskId));
    }
}

// ============================================================================
// Phase 4: THE UNIFICATION LOGIC (The "Driver")
// ============================================================================

use hwml_core::common::UniverseLevel;
use hwml_core::syn::Syntax;

/// Async unification function.
/// Instead of returning a Blocker, this function uses .await to suspend when blocked.
pub async fn unify<'db>(
    ctx: ContextHandle<'db>,
    lhs: RcSyntax<'db>,
    rhs: RcSyntax<'db>,
    ty: RcSyntax<'db>,
) -> Result<(), String> {
    println!("[Unify] Unifying {:?} == {:?}", lhs, rhs);

    // If they're already equal, we're done
    if lhs == rhs {
        println!("[Unify] Terms are already equal");
        return Ok(());
    }

    // Handle Pi injectivity: Pi x y == Pi a b => x == a && y == b
    if let Syntax::Pi(pi1) = &*lhs {
        if let Syntax::Pi(pi2) = &*rhs {
            println!("[Unify] Pi injectivity");
            // Unify domains
            Box::pin(unify(
                ctx.clone(),
                pi1.source.clone(),
                pi2.source.clone(),
                ty.clone(),
            ))
            .await?;

            // Unify codomains
            Box::pin(unify(
                ctx.clone(),
                pi1.target.clone(),
                pi2.target.clone(),
                ty.clone(),
            ))
            .await?;

            return Ok(());
        }
    }

    // Handle metavariable on the left side
    if let Syntax::Metavariable(meta) = &*lhs {
        println!("[Unify] Left side is metavariable {}", meta.id);

        // Check if the meta is already solved
        let maybe_resolved = {
            let state = ctx.0.borrow();
            if meta.id.0 < state.metas.len() {
                state.metas[meta.id.0].solution.clone()
            } else {
                None
            }
        };

        if let Some(resolved) = maybe_resolved {
            // Meta is already solved, unify the resolved value with the right side
            println!(
                "[Unify] Meta {} already solved, unifying resolved value",
                meta.id
            );
            return Box::pin(unify(ctx, resolved, rhs, ty)).await;
        } else {
            // Meta is not solved, solve it with the right side
            // In a full implementation, we'd need to do occurs check, etc.
            println!("[Unify] Solving meta {} with right side", meta.id);
            ctx.define_meta(meta.id, rhs.clone());
            return Ok(());
        }
    }

    // Handle metavariable on the right side
    if let Syntax::Metavariable(meta) = &*rhs {
        println!("[Unify] Right side is metavariable {}", meta.id);

        // Check if the meta is already solved
        let maybe_resolved = {
            let state = ctx.0.borrow();
            if meta.id.0 < state.metas.len() {
                state.metas[meta.id.0].solution.clone()
            } else {
                None
            }
        };

        if let Some(resolved) = maybe_resolved {
            // Meta is already solved, unify the left side with the resolved value
            println!(
                "[Unify] Meta {} already solved, unifying with resolved value",
                meta.id
            );
            return Box::pin(unify(ctx, lhs, resolved, ty)).await;
        } else {
            // Meta is not solved, solve it with the left side
            // In a full implementation, we'd need to do occurs check, etc.
            println!("[Unify] Solving meta {} with left side", meta.id);
            ctx.define_meta(meta.id, lhs.clone());
            return Ok(());
        }
    }

    // Handle application injectivity: f x == g y => f == g && x == y
    if let Syntax::Application(app1) = &*lhs {
        if let Syntax::Application(app2) = &*rhs {
            println!("[Unify] Application injectivity");

            // Unify functions
            Box::pin(unify(
                ctx.clone(),
                app1.function.clone(),
                app2.function.clone(),
                Syntax::universe_rc(UniverseLevel::new(0)), // Placeholder type
            ))
            .await?;

            // Unify arguments
            Box::pin(unify(
                ctx.clone(),
                app1.argument.clone(),
                app2.argument.clone(),
                Syntax::universe_rc(UniverseLevel::new(0)), // Placeholder type
            ))
            .await?;

            return Ok(());
        }
    }

    // If we get here, we couldn't unify
    Err(format!("Cannot unify {:?} with {:?}", lhs, rhs))
}

// ============================================================================
// Phase 5: HIGH-LEVEL API (The Elaborator)
// ============================================================================

/// Solve a list of constraints (futures) until completion or error.
pub fn solve_constraints<'db>(
    _ctx: ContextHandle<'db>,
    exec: &mut SingleThreadedExecutor<'db>,
) -> Result<(), String> {
    println!("[solve_constraints] Running executor");
    exec.run()?;

    println!("[solve_constraints] Executor completed successfully");
    Ok(())
}

// ============================================================================
// TESTS AND EXAMPLES
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_meta_solving() {
        let ctx = ContextHandle::new();

        // Allocate a metavariable through the context
        let meta0 = ctx.fresh_meta();

        // Create a simple constraint that solves a meta
        async fn solve_meta(ctx: ContextHandle<'_>, meta: MetaVariableId) -> Result<(), String> {
            println!("(Task) Solving meta {}", meta);
            let term = Syntax::universe_rc(UniverseLevel::new(0));
            ctx.define_meta(meta, term);
            Ok(())
        }

        let mut exec = SingleThreadedExecutor::new();
        exec.spawn(solve_meta(ctx.clone(), meta0));

        let result = solve_constraints(ctx.clone(), &mut exec);
        assert!(result.is_ok());

        // Check that meta0 was solved
        let solution = ctx.get_solution(meta0);
        assert!(solution.is_some(), "meta0 should be solved");
    }

    #[test]
    fn test_dependent_constraints() {
        let ctx = ContextHandle::new();

        // Allocate metavariables through the context
        let meta0 = ctx.fresh_meta();
        let meta1 = ctx.fresh_meta();

        // Task A waits for meta 0, then solves meta 1
        async fn task_a(
            ctx: ContextHandle<'_>,
            meta0: MetaVariableId,
            meta1: MetaVariableId,
        ) -> Result<(), String> {
            println!("(Task A) Waiting for meta {}", meta0);
            let val = WaitForResolved::new(ctx.clone(), meta0).await;
            println!("(Task A) Meta {} resolved to {:?}", meta0, val);

            // Now solve meta 1
            ctx.define_meta(meta1, Syntax::universe_rc(UniverseLevel::new(1)));
            Ok(())
        }

        // Task B solves meta 0
        async fn task_b(ctx: ContextHandle<'_>, meta0: MetaVariableId) -> Result<(), String> {
            println!("(Task B) Solving meta {}", meta0);
            ctx.define_meta(meta0, Syntax::universe_rc(UniverseLevel::new(0)));
            Ok(())
        }

        let mut exec = SingleThreadedExecutor::new();
        exec.spawn(task_a(ctx.clone(), meta0, meta1));
        exec.spawn(task_b(ctx.clone(), meta0));

        let result = solve_constraints(ctx.clone(), &mut exec);

        assert!(result.is_ok());

        // Check that both metas were solved
        let solution0 = ctx.get_solution(meta0);
        let solution1 = ctx.get_solution(meta1);
        assert!(solution0.is_some(), "meta0 should be solved");
        assert!(solution1.is_some(), "meta1 should be solved");
    }

    #[test]
    fn test_unification() {
        let ctx = ContextHandle::new();

        // Allocate a metavariable through the context
        let meta0 = ctx.fresh_meta();

        async fn unify_task(ctx: ContextHandle<'_>, meta0: MetaVariableId) -> Result<(), String> {
            // Create two terms with a metavariable
            let meta = Syntax::metavariable_rc(meta0, vec![]);
            let universe = Syntax::universe_rc(UniverseLevel::new(0));

            // Unify meta with universe
            unify(ctx, meta, universe.clone(), universe).await
        }

        let mut exec = SingleThreadedExecutor::new();
        exec.spawn(unify_task(ctx.clone(), meta0));

        let result = solve_constraints(ctx.clone(), &mut exec);

        assert!(result.is_ok());

        // Check that meta0 was solved
        let solution = ctx.get_solution(meta0);
        assert!(solution.is_some(), "meta0 should be solved");
    }
}
