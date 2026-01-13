use hwml_core::check::TCEnvironment;
use hwml_core::common::MetaVariableId;
use hwml_core::val::{GlobalEnv, Value};
use slab::Slab;
use std::cell::RefCell;
use std::collections::VecDeque;
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

// ============================================================================
// RICH DEPENDENCY TRACKING
// ============================================================================

/// Describes why a task is blocked on a metavariable.
/// This enables rich error reporting by capturing the context of each dependency.
#[derive(Debug, Clone)]
pub enum BlockReason {
    /// A simple textual description of why we're blocked
    Generic(String),
    /// We expect the metavariable to have a specific shape (e.g., "Function", "Pi type")
    ExpectedShape(String),
    /// We're blocked because we're trying to unify two terms
    Unifying(String, String), // Store debug strings instead of values to avoid lifetime issues
}

impl BlockReason {
    /// Create a generic blocking reason with a description
    pub fn generic(description: impl Into<String>) -> Self {
        BlockReason::Generic(description.into())
    }

    /// Create a blocking reason indicating we expect a specific shape
    pub fn expected_shape(shape: impl Into<String>) -> Self {
        BlockReason::ExpectedShape(shape.into())
    }
}

/// Information about a task waiting on a metavariable.
/// Contains the waker to resume the task and the reason for waiting.
#[derive(Clone)]
struct WaitingTask {
    /// The waker to resume this task when the metavariable is solved
    waker: Waker,
    /// Why this task is waiting on this metavariable
    reason: BlockReason,
}

type TaskId = usize;

/// Information stored for each metavariable slot.
#[derive(Clone)]
struct MetaSlot<'db> {
    /// The solution for this metavariable, if solved
    solution: Option<Rc<Value<'db>>>,
    /// Tasks waiting for this metavariable to be solved, with reasons
    waiters: Vec<WaitingTask>,
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
    /// register the waker with the reason and return None.
    fn poll_meta(
        &mut self,
        meta: MetaVariableId,
        waker: &Waker,
        reason: BlockReason,
    ) -> Option<Rc<Value<'db>>> {
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
                slot.waiters.push(WaitingTask {
                    waker: waker.clone(),
                    reason,
                });
                None
            }
        }
    }

    /// Get all unsolved metavariables with their waiting tasks.
    /// Used for generating detailed error reports when the solver stalls.
    pub fn get_unsolved_with_waiters(&self) -> Vec<(MetaVariableId, Vec<BlockReason>)> {
        self.metas
            .iter()
            .enumerate()
            .filter_map(|(idx, slot)| {
                if slot.solution.is_none() && !slot.waiters.is_empty() {
                    let reasons = slot
                        .waiters
                        .iter()
                        .map(|w| w.reason.clone())
                        .collect::<Vec<_>>();
                    Some((MetaVariableId(idx), reasons))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Get the solution for a specific metavariable, if it has been solved.
    pub fn get_solution(&self, meta: MetaVariableId) -> Option<Rc<Value<'db>>> {
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
    pub fn get_substitution(&self) -> Vec<Option<Rc<Value<'db>>>> {
        self.metas
            .iter()
            .map(|slot| slot.solution.clone())
            .collect()
    }
}

/// A shared handle to the solver state.
/// This is cloned and passed to all constraint futures.
#[derive(Clone)]
pub struct SolverEnvironment<'g, 'db> {
    /// Shared reference to the solver state
    pub state: Rc<RefCell<SolverState<'db>>>,
    /// Type-checking environment for evaluation and type checking
    pub tc_env: Rc<TCEnvironment<'g, 'db>>,
    /// Task spawner for spawning concurrent unification tasks
    pub spawner: TaskSpawner<'db>,
}

impl<'g, 'db> SolverEnvironment<'g, 'db> {
    /// Create a new context handle with the given type-checking environment and spawner
    pub fn new(tc_env: TCEnvironment<'g, 'db>, spawner: TaskSpawner<'db>) -> Self {
        SolverEnvironment {
            state: Rc::new(RefCell::new(SolverState::new())),
            tc_env: Rc::new(tc_env),
            spawner,
        }
    }

    /// Attempt to read a meta. If solved, return value.
    /// If not, register the current Waker with reason and return None.
    pub fn poll_meta(
        &self,
        meta: MetaVariableId,
        waker: &Waker,
        reason: BlockReason,
    ) -> Option<Rc<Value<'db>>> {
        self.state.borrow_mut().poll_meta(meta, waker, reason)
    }

    /// Allocate a fresh metavariable.
    pub fn fresh_meta(&self) -> MetaVariableId {
        self.state.borrow_mut().fresh_meta()
    }

    /// Get the solution for a specific metavariable, if it has been solved.
    pub fn get_solution(&self, meta: MetaVariableId) -> Option<Rc<Value<'db>>> {
        self.state.borrow().get_solution(meta)
    }

    /// Solve a meta and wake everyone up
    pub fn define_meta(&self, meta: MetaVariableId, value: Rc<Value<'db>>) {
        // We need to be careful here to avoid holding the borrow when waking
        let waiting_tasks = {
            let mut state = self.state.borrow_mut();
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
        if !waiting_tasks.is_empty() {
            println!(
                "[Solver] Waking {} tasks waiting on {}",
                waiting_tasks.len(),
                meta
            );
            for waiting_task in waiting_tasks {
                waiting_task.waker.wake();
            }
        }
    }

    /// Get the final substitution as a vector indexed by MetaVariableId.
    ///
    /// Returns a Vec where `result[meta.0]` gives the solution for `meta`.
    /// Unsolved metas have `None` at their index.
    pub fn get_substitution(&self) -> Vec<Option<Rc<Value<'db>>>> {
        self.state.borrow().get_substitution()
    }

    /// Generate a detailed blame report for unsolved metavariables.
    /// This is called when the solver stalls to provide rich error messages.
    pub fn generate_blame_report(&self) -> String {
        let unsolved = self.state.borrow().get_unsolved_with_waiters();

        if unsolved.is_empty() {
            return String::from("No unsolved metavariables with waiting tasks.");
        }

        let mut report = String::from("=== UNSOLVED CONSTRAINTS ===\n");

        for (meta_id, waiters) in unsolved {
            report.push_str(&format!("\n{} is unsolved.\n", meta_id));
            report.push_str("   Blocked for the following reasons:\n");

            for reason in waiters {
                let reason_str = match reason {
                    BlockReason::Generic(desc) => desc,
                    BlockReason::ExpectedShape(shape) => {
                        format!("Expected shape: {}", shape)
                    }
                    BlockReason::Unifying(lhs, rhs) => {
                        format!("Unifying {:?} with {:?}", lhs, rhs)
                    }
                };
                report.push_str(&format!("   - {}\n", reason_str));
            }
        }

        report
    }
}

/// A Future that blocks until a specific MetaVar is solved.
/// This replaces the `BlockOnMeta` constructor in Haskell.
/// Now includes a reason for blocking to enable rich error reporting.
pub struct WaitForResolved<'g, 'db> {
    ctx: SolverEnvironment<'g, 'db>,
    meta: MetaVariableId,
    reason: BlockReason,
}

impl<'g, 'db> WaitForResolved<'g, 'db> {
    /// Create a new future that waits for a metavariable to be resolved.
    ///
    /// # Arguments
    /// * `ctx` - The solver context
    /// * `meta` - The metavariable to wait for
    /// * `reason` - Why we're waiting (for error reporting)
    pub fn new(ctx: SolverEnvironment<'g, 'db>, meta: MetaVariableId, reason: BlockReason) -> Self {
        WaitForResolved { ctx, meta, reason }
    }
}

impl<'g, 'db> Future for WaitForResolved<'g, 'db> {
    type Output = Rc<Value<'db>>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self
            .ctx
            .poll_meta(self.meta, cx.waker(), self.reason.clone())
        {
            Some(term) => {
                println!("[WaitForResolved] Meta {} is resolved", self.meta);
                Poll::Ready(term)
            }
            None => {
                println!(
                    "[WaitForResolved] Blocked waiting on {} (reason: {:?})",
                    self.meta, self.reason
                );
                Poll::Pending
            }
        }
    }
}

/// The structure shared between the Executor and the Wakers.
/// Contains the queue of tasks that are ready to run.
struct ReadyQueue {
    queue: RefCell<VecDeque<TaskId>>,
}

/// Shared task storage that can be accessed by both the executor and spawner.
struct TaskStorage<'db> {
    /// All spawned tasks, indexed by TaskId using a Slab allocator
    tasks: RefCell<Slab<Pin<Box<dyn Future<Output = Result<(), String>> + 'db>>>>,
    /// Queue of task IDs that are ready to run
    ready_queue: Rc<ReadyQueue>,
}

/// A handle that allows spawning new tasks from within async functions.
/// This is cloned and passed through the SolverEnvironment.
#[derive(Clone)]
pub struct TaskSpawner<'db> {
    storage: Rc<TaskStorage<'db>>,
}

impl<'db> TaskSpawner<'db> {
    /// Spawn a new task that will be executed by the executor.
    pub fn spawn<F>(&self, future: F)
    where
        F: Future<Output = Result<(), String>> + 'db,
    {
        let mut tasks = self.storage.tasks.borrow_mut();
        let id = tasks.insert(Box::pin(future));
        self.storage.ready_queue.queue.borrow_mut().push_back(id);
        println!("[Spawner] Spawned task {}", id);
    }
}

/// A lightweight, single-threaded executor for constraint solving.
pub struct SingleThreadedExecutor<'db> {
    /// Shared storage for tasks
    storage: Rc<TaskStorage<'db>>,
}

#[allow(unsafe_code)]
impl<'db> SingleThreadedExecutor<'db> {
    pub fn new() -> Self {
        let ready_queue = Rc::new(ReadyQueue {
            queue: RefCell::new(VecDeque::new()),
        });
        Self {
            storage: Rc::new(TaskStorage {
                tasks: RefCell::new(Slab::new()),
                ready_queue,
            }),
        }
    }

    /// Get a spawner handle that can be used to spawn tasks from within async functions.
    pub fn spawner(&self) -> TaskSpawner<'db> {
        TaskSpawner {
            storage: self.storage.clone(),
        }
    }

    /// Spawn a new constraint task
    pub fn spawn<F>(&mut self, future: F)
    where
        F: Future<Output = Result<(), String>> + 'db,
    {
        // Slab automatically allocates the next available slot
        let mut tasks = self.storage.tasks.borrow_mut();
        let id = tasks.insert(Box::pin(future));
        self.storage.ready_queue.queue.borrow_mut().push_back(id);
        println!("[Executor] Spawned task {}", id);
    }

    /// The main loop. Runs until all tasks are done or stalled.
    /// Returns Ok if all tasks completed successfully.
    /// Returns Err if any task failed or if there's a deadlock.
    pub fn run<'g>(&mut self, ctx: &SolverEnvironment<'g, 'db>) -> Result<(), String> {
        println!("[Executor] Starting execution");

        loop {
            // Pop from the queue without holding the borrow
            let task_id = self.storage.ready_queue.queue.borrow_mut().pop_front();

            let Some(task_id) = task_id else {
                break; // Queue is empty
            };

            let waker = self.create_waker(task_id);
            let mut context = Context::from_waker(&waker);

            // Use get_mut() to poll in-place - avoids remove/insert churn
            let mut tasks = self.storage.tasks.borrow_mut();
            if let Some(task) = tasks.get_mut(task_id) {
                match task.as_mut().poll(&mut context) {
                    Poll::Ready(Ok(())) => {
                        println!("[Executor] Task {} finished successfully", task_id);
                        // Only remove when done - this frees the slot for reuse
                        let _ = tasks.remove(task_id);
                    }
                    Poll::Ready(Err(e)) => {
                        println!("[Executor] Task {} failed: {}", task_id, e);
                        let _ = tasks.remove(task_id);
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
        let tasks = self.storage.tasks.borrow();
        if !tasks.is_empty() {
            let pending_tasks: Vec<_> = tasks.iter().map(|(id, _)| id).collect();
            let blame_report = ctx.generate_blame_report();
            return Err(format!(
                "Deadlock detected: {} tasks still pending but no progress can be made.\nPending tasks: {:?}\n\n{}",
                tasks.len(),
                pending_tasks,
                blame_report
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
        let data = Box::new((self.storage.ready_queue.clone(), task_id));
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
