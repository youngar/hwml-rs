use check::TCEnvironment;
use hwml_core::*;
use slab::Slab;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/// Evaluate the full type of a metavariable with its argument telescope.
/// For a metavariable `?M : (x : A) (y : B) : C`, this returns `Pi(A, \x. Pi(B, \y. C))`.
fn eval_metavariable_type<'db>(
    global: &val::GlobalEnv<'db>,
    info: &val::MetavariableInfo<'db>,
) -> Result<Rc<Value<'db>>, eval::Error> {
    use hwml_core::val::Environment;

    let mut env = Environment::new(global);

    // We build the Pi type recursively from the inside out.
    // First, evaluate all argument types and store them along with fresh variables.
    let mut arg_types = Vec::new();
    for arg_ty_syn in info.arguments.iter() {
        let arg_ty = eval::eval(&mut env, arg_ty_syn)?;
        arg_types.push(arg_ty.clone());
        // Push a fresh variable for this argument
        env.push_var(arg_ty);
    }

    // Now evaluate the result type in the fully extended environment
    let result_ty = eval::eval(&mut env, &info.ty)?;

    // Build the Pi type by wrapping from the inside out
    // We go backwards through the arguments
    let mut current_ty = result_ty;
    for (i, arg_ty) in arg_types.into_iter().enumerate().rev() {
        // Create a closure for the target type
        // The closure captures the current local environment up to this point
        // and the body is the current type as syntax
        //
        // For simplicity, we use a Value::Pi directly with the evaluated types
        let closure = val::Closure::new(
            val::LocalEnv::new(),
            quote_value_simple(global, i, &current_ty),
        );
        current_ty = Rc::new(Value::pi(arg_ty, closure));
    }

    Ok(current_ty)
}

/// Simple quoting function for building closures - just quotes a value back to syntax.
/// This is a simplified version that handles common cases.
fn quote_value_simple<'db>(
    _global: &val::GlobalEnv<'db>,
    _depth: usize,
    value: &Rc<Value<'db>>,
) -> syn::RcSyntax<'db> {
    // For now, we can just return a placeholder - the key is that the type
    // is stored semantically. In practice, this closure won't be evaluated
    // directly, but used for typing information.
    // A proper implementation would use the full quote function.
    match value.as_ref() {
        Value::Universe(u) => syn::Syntax::universe_rc(u.level),
        // For other cases, we'll need to handle them as they come up
        _ => syn::Syntax::universe_rc(UniverseLevel::new(0)), // Placeholder
    }
}

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
    /// The type of the metavariable.
    ty: Rc<Value<'db>>,
    /// The solution for this metavariable, if solved.
    solution: Option<Rc<Syntax<'db>>>,
    /// Tasks waiting for this metavariable to be solved.
    waiters: Vec<WaitingTask>,
    /// Whether this metavariable is poisoned (represents an error).
    /// Poisoned metavariables unify with anything to prevent error cascades.
    poisoned: bool,
}

impl<'db> MetaSlot<'db> {
    fn new(ty: Rc<Value<'db>>) -> Self {
        Self {
            ty,
            solution: None,
            waiters: Vec::new(),
            poisoned: false,
        }
    }

    fn new_poisoned(ty: Rc<Value<'db>>) -> Self {
        Self {
            ty,
            solution: None,
            waiters: Vec::new(),
            poisoned: true,
        }
    }

    fn is_solved(&self) -> bool {
        self.solution.is_some()
    }

    fn is_poisoned(&self) -> bool {
        self.poisoned
    }
}

/// The central state for the constraint solver. Contains solved metavariables
/// and wait lists for blocked tasks.
pub struct SolverState<'db> {
    /// HashMap of metavariable slots, indexed by MetaVariableId
    /// Each slot contains the solution (if solved) and list of waiting tasks
    metas: HashMap<MetaVariableId, MetaSlot<'db>>,

    /// Dependency graph: meta ?M depends on metas in the set
    /// Edge ?M -> ?N means "?M's solution mentions ?N"
    dependencies: HashMap<MetaVariableId, HashSet<MetaVariableId>>,

    /// Counter for generating metavariable indices
    next_meta_index: u16,
}

impl<'db> SolverState<'db> {
    pub fn new() -> Self {
        Self {
            metas: HashMap::new(),
            dependencies: HashMap::new(),
            next_meta_index: 0,
        }
    }

    /// Allocate a fresh metavariable.
    ///
    /// This is the **only** way to create new MetaVariableIds for this solver.
    /// By allocating through the state, we ensure deterministic ID generation.
    pub fn fresh_meta(&mut self, ty: Rc<Value<'db>>) -> MetaVariableId {
        let local_index = self.next_meta_index;
        let id = MetaVariableId::new(local_index);
        self.next_meta_index += 1;

        self.metas.insert(id, MetaSlot::new(ty));
        println!("[Solver] Allocated fresh meta {}", id);
        id
    }

    /// Allocate a fresh poisoned metavariable (for error recovery).
    pub fn fresh_poisoned_meta(&mut self, ty: Rc<Value<'db>>) -> MetaVariableId {
        let local_index = self.next_meta_index;
        let id = MetaVariableId::new(local_index);
        self.next_meta_index += 1;

        self.metas.insert(id, MetaSlot::new_poisoned(ty));
        println!("[Solver] Allocated fresh poisoned meta {}", id);
        id
    }

    /// Attempt to read a meta. If solved, return the value. If not solved,
    /// register the waker with the reason and return None.
    fn poll_meta(
        &mut self,
        meta: MetaVariableId,
        waker: &Waker,
        reason: BlockReason,
    ) -> Option<Rc<Syntax<'db>>> {
        // Meta should already exist if it was allocated through fresh_meta
        let slot = self.metas.get_mut(&meta).expect(&format!(
            "Meta {} not allocated! Use fresh_meta() to allocate metavariables.",
            meta
        ));

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
            .filter_map(|(id, slot)| {
                if slot.solution.is_none() && !slot.waiters.is_empty() {
                    let reasons = slot
                        .waiters
                        .iter()
                        .map(|w| w.reason.clone())
                        .collect::<Vec<_>>();
                    Some((*id, reasons))
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn is_solved(&self, id: MetaVariableId) -> bool {
        self.metas
            .get(&id)
            .map_or(false, |slot| slot.solution.is_some())
    }

    pub fn is_poisoned(&self, id: MetaVariableId) -> bool {
        self.metas.get(&id).map_or(false, |slot| slot.poisoned)
    }

    /// Get the solution for a specific metavariable, if it has been solved.
    pub fn solution(&self, id: MetaVariableId) -> Option<Rc<Syntax<'db>>> {
        self.metas.get(&id).and_then(|slot| slot.solution.clone())
    }

    /// Get the type of a metavariable.
    pub fn meta_type(&self, id: MetaVariableId) -> Rc<Value<'db>> {
        self.metas
            .get(&id)
            .expect(&format!("Meta {} not found", id))
            .ty
            .clone()
    }

    /// Collect all metavariables that appear in a syntax term.
    /// This is used to build the dependency graph when solving a metavariable.
    fn collect_dependencies(&self, term: &Syntax<'db>) -> HashSet<MetaVariableId> {
        let mut deps = HashSet::new();

        fn collect_rec<'db>(term: &Syntax<'db>, deps: &mut HashSet<MetaVariableId>) {
            match term {
                Syntax::Metavariable(meta) => {
                    deps.insert(meta.id);
                    for arg in meta.substitution.iter() {
                        collect_rec(arg, deps);
                    }
                }
                Syntax::Variable(_) => {}
                Syntax::Constant(_) => {}
                Syntax::Universe(_) => {}
                Syntax::Prim(_) => {}
                Syntax::HardwareUniverse(_) => {}
                Syntax::SignalUniverse(_) => {}
                Syntax::ModuleUniverse(_) => {}
                Syntax::Bit(_) => {}
                Syntax::Zero(_) => {}
                Syntax::One(_) => {}
                Syntax::Pi(pi) => {
                    collect_rec(&pi.source, deps);
                    collect_rec(&pi.target, deps);
                }
                Syntax::Lambda(lam) => {
                    collect_rec(&lam.body, deps);
                }
                Syntax::Application(app) => {
                    collect_rec(&app.function, deps);
                    collect_rec(&app.argument, deps);
                }
                Syntax::Lift(lift) => {
                    collect_rec(&lift.ty, deps);
                }
                Syntax::SLift(slift) => {
                    collect_rec(&slift.ty, deps);
                }
                Syntax::MLift(mlift) => {
                    collect_rec(&mlift.ty, deps);
                }
                Syntax::TypeConstructor(tc) => {
                    for arg in tc.arguments.iter() {
                        collect_rec(arg, deps);
                    }
                }
                Syntax::DataConstructor(dc) => {
                    for arg in dc.arguments.iter() {
                        collect_rec(arg, deps);
                    }
                }
                Syntax::Case(case) => {
                    // scrutinee is a Variable, not a Syntax - no need to recurse
                    // Case doesn't have a ty field - just recurse into branches
                    for branch in case.branches.iter() {
                        collect_rec(&branch.body, deps);
                    }
                }
                Syntax::Let(let_expr) => {
                    collect_rec(&let_expr.ty, deps);
                    collect_rec(&let_expr.value, deps);
                    collect_rec(&let_expr.body, deps);
                }
                Syntax::Eq(eq) => {
                    collect_rec(&eq.ty, deps);
                    collect_rec(&eq.lhs, deps);
                    collect_rec(&eq.rhs, deps);
                }
                Syntax::Refl(_) => {}
                Syntax::Transport(transport) => {
                    collect_rec(&transport.motive.body, deps);
                    collect_rec(&transport.proof, deps);
                    collect_rec(&transport.value, deps);
                }
                Syntax::Closure(closure) => {
                    collect_rec(&closure.body, deps);
                }
                Syntax::HArrow(harrow) => {
                    collect_rec(&harrow.source, deps);
                    collect_rec(&harrow.target, deps);
                }
                Syntax::Module(module) => {
                    collect_rec(&module.body, deps);
                }
                Syntax::HApplication(happ) => {
                    collect_rec(&happ.module, deps);
                    collect_rec(&happ.module_ty, deps);
                    collect_rec(&happ.argument, deps);
                }
                Syntax::Prim(_) => {}
                Syntax::Check(check) => {
                    collect_rec(&check.ty, deps);
                    collect_rec(&check.term, deps);
                }
            }
        }

        collect_rec(term, &mut deps);
        deps
    }

    /// Check if solving meta ?M with the given solution would create a cycle.
    /// Returns Ok(()) if no cycle, Err with the cycle path if a cycle is detected.
    fn check_cycle(
        &self,
        meta: MetaVariableId,
        solution_deps: &HashSet<MetaVariableId>,
    ) -> Result<(), Vec<MetaVariableId>> {
        // If the solution mentions the meta itself, that's an immediate cycle
        if solution_deps.contains(&meta) {
            return Err(vec![meta]);
        }

        // Check for transitive cycles: if ?M depends on ?N, and ?N (transitively) depends on ?M
        for &dep in solution_deps.iter() {
            if self.has_path(dep, meta, &mut HashSet::new()) {
                return Err(vec![meta, dep]);
            }
        }

        Ok(())
    }

    /// Check if there's a path from `from` to `to` in the dependency graph.
    /// Uses DFS with a visited set to detect cycles.
    fn has_path(
        &self,
        from: MetaVariableId,
        to: MetaVariableId,
        visited: &mut HashSet<MetaVariableId>,
    ) -> bool {
        if from == to {
            return true;
        }

        if visited.contains(&from) {
            return false;
        }

        visited.insert(from);

        if let Some(deps) = self.dependencies.get(&from) {
            for &dep in deps.iter() {
                if self.has_path(dep, to, visited) {
                    return true;
                }
            }
        }

        false
    }

    /// Test-only: Directly set a metavariable solution without cycle checking.
    /// This is useful for testing zonking and other functionality.
    #[cfg(test)]
    pub fn set_solution_unchecked(&mut self, meta: MetaVariableId, solution: Rc<Syntax<'db>>) {
        if let Some(slot) = self.metas.get_mut(&meta) {
            slot.solution = Some(solution);
        }
    }
}

/// Test-only: Initialize solver state from declared metavariables in GlobalEnv.
/// This is useful for testing unification/type-checking with metavariables
/// declared in a prelude, without going through full elaboration.
#[cfg(test)]
impl<'db> SolverState<'db> {
    /// Initialize the solver state with metavariables from the global environment.
    /// This evaluates the types of each declared metavariable and creates slots for them.
    pub fn from_global_env(global: &val::GlobalEnv<'db>) -> Self {
        use hwml_core::val::Environment;

        let mut metas = HashMap::new();
        let placeholder_ty = Rc::new(Value::universe(UniverseLevel::new(0)));

        // Populate with actual metavariable types
        for (id, info) in global.iter_metavariables() {
            // For a metavariable with arguments, we need to build a Pi type.
            // For now, just evaluate the final type in an extended environment.
            // The full type of ?M : (x : A) (y : B) : C is Pi(A, \x. Pi(B, \y. C))
            let mut env = Environment::new(global);

            // Build the Pi type by going through arguments in order
            // and wrapping the result type in Pi abstractions
            let ty = if info.arguments.len() == 0 {
                // No arguments, just evaluate the result type
                eval::eval(&mut env, &info.ty).unwrap_or(placeholder_ty.clone())
            } else {
                // Evaluate the full type by building up Pi types
                // We need to evaluate each argument type and the result type
                // in the appropriate context.
                eval_metavariable_type(global, info).unwrap_or(placeholder_ty.clone())
            };

            metas.insert(*id, MetaSlot::new(ty));
        }

        Self {
            metas,
            dependencies: HashMap::new(),
            next_meta_index: 0,
        }
    }
}

/// A shared handle to the solver state.
/// This is cloned and passed to all constraint futures.
#[derive(Clone)]
pub struct SolverEnvironment<'db, 'g> {
    /// Shared reference to the solver state
    pub state: Rc<RefCell<SolverState<'db>>>,
    /// Type-checking environment for evaluation and type checking
    pub tc_env: TCEnvironment<'db, 'g>,
    /// Task spawner for spawning concurrent unification tasks
    pub spawner: TaskSpawner<'db>,
}

impl<'db, 'g> SolverEnvironment<'db, 'g> {
    /// Create a new context handle with an empty solver state.
    /// Use this for production elaboration where metavariables are created dynamically.
    pub fn new(tc_env: TCEnvironment<'db, 'g>, spawner: TaskSpawner<'db>) -> Self {
        SolverEnvironment {
            state: Rc::new(RefCell::new(SolverState::new())),
            tc_env,
            spawner,
        }
    }
}

/// Test-only: Initialize solver environment from declared metavariables in GlobalEnv.
#[cfg(test)]
impl<'db, 'g> SolverEnvironment<'db, 'g> {
    /// Create a new context handle, initializing solver state from declared metavariables.
    /// This is useful for testing unification/type-checking with metavariables
    /// declared in a prelude, without going through full elaboration.
    pub fn new_from_global(tc_env: TCEnvironment<'db, 'g>, spawner: TaskSpawner<'db>) -> Self {
        let state = SolverState::from_global_env(tc_env.values.global);
        SolverEnvironment {
            state: Rc::new(RefCell::new(state)),
            tc_env,
            spawner,
        }
    }
}

impl<'db, 'g> SolverEnvironment<'db, 'g> {
    /// Attempt to read a meta. If solved, return value.
    /// If not, register the current Waker with reason and return None.
    pub fn poll_meta(
        &self,
        meta: MetaVariableId,
        waker: &Waker,
        reason: BlockReason,
    ) -> Option<Rc<Syntax<'db>>> {
        self.state.borrow_mut().poll_meta(meta, waker, reason)
    }

    /// Allocate a fresh metavariable and return its ID.
    /// The type is stored in the SolverState's MetaSlot.
    /// TODO: Accept a Location parameter once we add location tracking to the elaboration context.
    pub fn fresh_meta_id(&self, ty: Rc<Value<'db>>) -> MetaVariableId {
        self.state.borrow_mut().fresh_meta(ty)
    }

    /// Allocate a fresh metavariable and return it as a Flex value.
    /// The metavariable captures the current local environment as its substitution.
    pub fn fresh_meta(&self, ty: Rc<Value<'db>>) -> Rc<Value<'db>> {
        let id = self.fresh_meta_id(ty.clone());
        Rc::new(Value::metavariable(
            id,
            self.tc_env.values.local.clone(),
            ty,
        ))
    }

    /// Allocate a fresh poisoned metavariable for error recovery.
    pub fn fresh_poisoned_meta(&self, ty: Rc<Value<'db>>) -> Rc<Value<'db>> {
        let id = self.state.borrow_mut().fresh_poisoned_meta(ty.clone());
        Rc::new(Value::metavariable(
            id,
            self.tc_env.values.local.clone(),
            ty,
        ))
    }

    /// Get the solution for a specific metavariable, if it has been solved.
    pub fn solution(&self, meta: MetaVariableId) -> Option<Rc<Syntax<'db>>> {
        self.state.borrow().solution(meta)
    }

    pub fn is_solved(&self, meta: MetaVariableId) -> bool {
        self.state.borrow().is_solved(meta)
    }

    /// Get the type of a metavariable.
    pub fn meta_type(&self, meta: MetaVariableId) -> Rc<Value<'db>> {
        self.state.borrow().meta_type(meta)
    }

    /// Solve a meta with cycle detection and dependency tracking.
    /// Returns Ok(()) if the solution is valid, Err with cycle path if a cycle is detected.
    pub fn solve_checked(
        &self,
        meta: MetaVariableId,
        value: Rc<Syntax<'db>>,
    ) -> Result<(), Vec<MetaVariableId>> {
        // First, check for cycles before committing the solution
        let (deps, cycle_check) = {
            let state = self.state.borrow();
            let deps = state.collect_dependencies(&value);
            let cycle_check = state.check_cycle(meta, &deps);
            (deps, cycle_check)
        };

        // If there's a cycle, return the error without solving
        cycle_check?;

        // No cycle detected, proceed with solving
        let waiting_tasks = {
            let mut state = self.state.borrow_mut();
            println!("[Solver] Defining {} := {:?}", meta, value);

            // Update the dependency graph
            state.dependencies.insert(meta, deps);

            // Get the slot and set the solution
            let slot = state.metas.get_mut(&meta).expect(&format!(
                "Meta {} not allocated! Use fresh_meta() to allocate metavariables.",
                meta
            ));
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

        Ok(())
    }

    /// Solve a meta and wake everyone up.
    /// This is the unchecked version that panics on cycles (for backward compatibility).
    /// New code should use `solve_checked` instead.
    pub fn solve(&self, meta: MetaVariableId, value: Rc<Syntax<'db>>) {
        if let Err(cycle) = self.solve_checked(meta, value) {
            panic!("Cycle detected when solving {}: {:?}", meta, cycle);
        }
    }

    /// Zonk a syntax term, replacing all solved metavariables with their solutions.
    /// This is a total function that never fails.
    pub fn zonk(&self, term: &Syntax<'db>) -> Rc<Syntax<'db>> {
        crate::zonk::zonk(&self.state.borrow(), term)
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
pub struct WaitForResolved<'db, 'g> {
    ctx: SolverEnvironment<'db, 'g>,
    meta: MetaVariableId,
    reason: BlockReason,
}

impl<'db, 'g> WaitForResolved<'db, 'g> {
    /// Create a new future that waits for a metavariable to be resolved.
    ///
    /// # Arguments
    /// * `ctx` - The solver context
    /// * `meta` - The metavariable to wait for
    /// * `reason` - Why we're waiting (for error reporting)
    pub fn new(ctx: SolverEnvironment<'db, 'g>, meta: MetaVariableId, reason: BlockReason) -> Self {
        WaitForResolved { ctx, meta, reason }
    }
}

impl<'db, 'g> Future for WaitForResolved<'db, 'g> {
    type Output = Rc<Syntax<'db>>;

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
    pub fn run<'g>(&mut self, ctx: &SolverEnvironment<'db, 'g>) -> Result<(), String> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use hwml_core::syn::Syntax;
    use hwml_core::val::Value;

    #[test]
    fn test_cycle_detection_direct() {
        // Test direct cycle: ?M := ?M
        let mut state = SolverState::new();
        let ty = Rc::new(Value::universe(hwml_core::common::UniverseLevel::new(0)));
        let meta_id = state.fresh_meta(ty);

        // Try to solve ?M := ?M (direct cycle)
        let solution = Syntax::metavariable_rc(meta_id, vec![]);
        let deps = state.collect_dependencies(&solution);
        let result = state.check_cycle(meta_id, &deps);

        assert!(result.is_err(), "Direct cycle should be detected");
    }

    #[test]
    fn test_cycle_detection_transitive() {
        // Test transitive cycle: ?M := ?N, ?N := ?M
        let mut state = SolverState::new();
        let ty = Rc::new(Value::universe(hwml_core::common::UniverseLevel::new(0)));

        let meta_m = state.fresh_meta(ty.clone());
        let meta_n = state.fresh_meta(ty.clone());

        // First solve ?N := ?M
        let solution_n = Syntax::metavariable_rc(meta_m, vec![]);
        let deps_n = state.collect_dependencies(&solution_n);
        state.dependencies.insert(meta_n, deps_n);

        // Now try to solve ?M := ?N (would create a cycle)
        let solution_m = Syntax::metavariable_rc(meta_n, vec![]);
        let deps_m = state.collect_dependencies(&solution_m);
        let result = state.check_cycle(meta_m, &deps_m);

        assert!(result.is_err(), "Transitive cycle should be detected");
    }

    #[test]
    fn test_no_cycle() {
        // Test valid dependency: ?M := ?N where ?N is independent
        let mut state = SolverState::new();
        let ty = Rc::new(Value::universe(hwml_core::common::UniverseLevel::new(0)));

        let meta_m = state.fresh_meta(ty.clone());
        let meta_n = state.fresh_meta(ty.clone());

        // Solve ?M := ?N (no cycle)
        let solution = Syntax::metavariable_rc(meta_n, vec![]);
        let deps = state.collect_dependencies(&solution);
        let result = state.check_cycle(meta_m, &deps);

        assert!(result.is_ok(), "No cycle should be detected");
    }

    #[test]
    fn test_poisoned_meta_creation() {
        let mut state = SolverState::new();
        let ty = Rc::new(Value::universe(hwml_core::common::UniverseLevel::new(0)));
        let meta_id = state.fresh_poisoned_meta(ty);

        assert!(state.is_poisoned(meta_id), "Meta should be poisoned");
        assert!(
            !state.is_solved(meta_id),
            "Poisoned meta should not be solved"
        );
    }

    #[test]
    fn test_location_derived_ids() {
        let mut state = SolverState::new();
        let ty = Rc::new(Value::universe(hwml_core::common::UniverseLevel::new(0)));

        // Create multiple metas at the same location
        let meta1 = state.fresh_meta(ty.clone());
        let meta2 = state.fresh_meta(ty.clone());
        let meta3 = state.fresh_meta(ty.clone());

        // They should have different local indices
        assert_ne!(meta1, meta2);
        assert_ne!(meta2, meta3);
        assert_ne!(meta1, meta3);
    }
}
