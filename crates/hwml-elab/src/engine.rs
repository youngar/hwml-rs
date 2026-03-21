use crate::*;
use hwml_core::val::LocalEnv;
use hwml_core::*;
use slab::Slab;
use std::cell::{Ref, RefCell};
use std::collections::VecDeque;
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

#[derive(Clone)]
struct WaitingTask {
    waker: Waker,
}

type TaskId = usize;

#[derive(Clone)]
struct MetaEntry<'db> {
    ty: RcValue<'db>,
    solution: Option<RcSyntax<'db>>,
    waiters: Vec<WaitingTask>,
    poisoned: bool,
    _source_range: Option<SourceRange<'db>>,
}

impl<'db> MetaEntry<'db> {
    fn new(ty: RcValue<'db>, source_range: Option<SourceRange<'db>>) -> Self {
        Self {
            ty,
            solution: None,
            waiters: Vec::new(),
            poisoned: false,
            _source_range: source_range,
        }
    }

    fn new_poisoned(ty: RcValue<'db>, source_range: Option<SourceRange<'db>>) -> Self {
        Self {
            ty,
            solution: None,
            waiters: Vec::new(),
            poisoned: true,
            _source_range: source_range,
        }
    }

    fn is_solved(&self) -> bool {
        self.solution.is_some()
    }

    fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    fn set_solution(&mut self, solution: RcSyntax<'db>) {
        match &self.solution {
            Some(_) => panic!("solution already set"),
            None => self.solution = Some(solution),
        }
    }

    fn poll_solution(&mut self, waker: &Waker) -> Option<RcSyntax<'db>> {
        match &self.solution {
            Some(term) => Some(term.clone()),
            None => {
                self.waiters.push(WaitingTask {
                    waker: waker.clone(),
                });
                None
            }
        }
    }
}

struct MetaTable<'db> {
    metas: Vec<MetaEntry<'db>>,
}

impl<'db> MetaTable<'db> {
    fn new() -> Self {
        Self { metas: Vec::new() }
    }

    pub fn fresh(
        &mut self,
        ty: RcValue<'db>,
        source_range: Option<SourceRange<'db>>,
    ) -> MetaVariableId {
        let id = MetaVariableId(self.metas.len());
        self.metas.push(MetaEntry::new(ty, source_range));
        id
    }

    pub fn fresh_poisoned(
        &mut self,
        ty: RcValue<'db>,
        source_range: Option<SourceRange<'db>>,
    ) -> MetaVariableId {
        let id = MetaVariableId(self.metas.len());
        self.metas.push(MetaEntry::new_poisoned(ty, source_range));
        id
    }

    fn is_solved(&self, id: MetaVariableId) -> bool {
        self.metas[id.0].is_solved()
    }

    fn is_poisoned(&self, id: MetaVariableId) -> bool {
        self.metas[id.0].is_poisoned()
    }

    fn set_solution(&mut self, id: MetaVariableId, solution: RcSyntax<'db>) {
        self.metas[id.0].set_solution(solution)
    }

    fn solution(&self, id: MetaVariableId) -> Option<RcSyntax<'db>> {
        self.metas[id.0].solution.clone()
    }

    fn poll_solution(&mut self, id: MetaVariableId, waker: &Waker) -> Option<RcSyntax<'db>> {
        self.metas[id.0].poll_solution(waker)
    }

    fn ty(&self, id: MetaVariableId) -> RcValue<'db> {
        self.metas[id.0].ty.clone()
    }
}

pub struct SolverState<'db> {
    pub global_env: GlobalEnv<'db>,
    pub meta_table: MetaTable<'db>,
}

impl<'db> SolverState<'db> {
    pub fn new() -> Self {
        Self {
            global_env: GlobalEnv::new(),
            meta_table: MetaTable::new(),
        }
    }

    pub fn with_global_env(global_env: GlobalEnv<'db>) -> Self {
        Self {
            global_env,
            meta_table: MetaTable::new(),
        }
    }

    pub fn finalize(self) -> GlobalEnv<'db> {
        self.global_env
    }

    pub fn fresh_meta(
        &mut self,
        ty: RcValue<'db>,
        source_range: Option<SourceRange<'db>>,
    ) -> MetaVariableId {
        self.meta_table.fresh(ty, source_range)
    }

    pub fn fresh_poisoned_meta(
        &mut self,
        ty: RcValue<'db>,
        source_range: Option<SourceRange<'db>>,
    ) -> MetaVariableId {
        self.meta_table.fresh_poisoned(ty, source_range)
    }

    pub fn is_meta_solved(&self, id: MetaVariableId) -> bool {
        self.meta_table.is_solved(id)
    }

    pub fn is_meta_poisoned(&self, id: MetaVariableId) -> bool {
        self.meta_table.is_poisoned(id)
    }

    pub fn meta_solution(&self, id: MetaVariableId) -> Option<RcSyntax<'db>> {
        self.meta_table.solution(id)
    }

    fn poll_meta_solution(&mut self, id: MetaVariableId, waker: &Waker) -> Option<RcSyntax<'db>> {
        self.meta_table.poll_solution(id, waker)
    }

    pub fn meta_type(&self, id: MetaVariableId) -> RcValue<'db> {
        self.meta_table.ty(id)
    }

    pub fn set_meta_solution(&mut self, id: MetaVariableId, solution: RcSyntax<'db>) {
        self.meta_table.set_solution(id, solution)
    }
}

#[derive(Clone, Debug)]
struct Locals<'db> {
    env: LocalEnv<'db>,
    tys: Vec<RcValue<'db>>,
}

impl<'db> Locals<'db> {
    fn new() -> Self {
        Locals {
            env: LocalEnv::new(),
            tys: Vec::new(),
        }
    }

    fn env(&self) -> &LocalEnv<'db> {
        &self.env
    }

    fn depth(&self) -> usize {
        self.env.depth()
    }

    fn value(&self, level: Level) -> &RcValue<'db> {
        &self.env[level]
    }

    fn ty(&self, level: Level) -> &RcValue<'db> {
        &self.tys[level.0]
    }

    fn push(&mut self, value: RcValue<'db>, ty: RcValue<'db>) {
        self.env.push(value);
        self.tys.push(ty);
    }

    fn pop(&mut self) {
        self.env.pop();
        self.tys.pop();
    }

    fn push_var(&mut self, ty: RcValue<'db>) -> RcValue<'db> {
        let var = Value::variable_rc(Level::new(self.depth()), ty.clone());
        self.push(var.clone(), ty);
        var
    }

    fn truncate(&mut self, depth: usize) {
        self.env.truncate(depth);
        self.tys.truncate(depth);
    }

    pub fn under_binder<F, R>(&mut self, _name: Option<Name>, ty: RcValue<'db>, f: F) -> Binding<R>
    where
        F: FnOnce(&mut Self) -> R,
    {
        let depth = self.depth();
        self.push_var(ty);
        let body = f(self);
        self.truncate(depth);
        Binding(body)
    }
}

#[derive(Clone)]
pub struct SolverEnvironment<'db> {
    pub db: &'db dyn salsa::Database,
    pub state: Rc<RefCell<SolverState<'db>>>,
    pub package: Option<QualifiedName<'db>>,
    pub dubbing_table: DubbingTable<'db>,
    pub locals: Locals<'db>,
    pub spawner: TaskSpawner<'db>,
}

impl<'db> SolverEnvironment<'db> {
    pub fn new(
        db: &'db dyn salsa::Database,
        state: Rc<RefCell<SolverState<'db>>>,
        spawner: TaskSpawner<'db>,
    ) -> Self {
        SolverEnvironment {
            db,
            state,
            package: None,
            dubbing_table: DubbingTable::new(),
            locals: Locals::new(),
            spawner,
        }
    }

    pub fn db(&self) -> &'db dyn salsa::Database {
        self.db
    }

    pub fn state(&self) -> Ref<'_, SolverState<'db>> {
        self.state.borrow()
    }

    pub fn global_env(&self) -> Ref<'_, GlobalEnv<'db>> {
        Ref::map(self.state(), |state| &state.global_env)
    }

    pub fn local_env(&self) -> &LocalEnv<'db> {
        self.locals.env()
    }

    pub fn child(&self) -> Self {
        self.clone()
    }

    pub fn spawn<F>(&self, future: F)
    where
        F: Future<Output = ()> + 'db,
    {
        self.spawner.spawn(future)
    }

    pub fn constrain<C>(&self, constraint: C)
    where
        C: Future<Output = ()> + 'db,
    {
        self.spawn(constraint)
    }

    pub fn depth(&self) -> usize {
        self.locals.depth()
    }

    pub fn value(&self, level: Level) -> &RcValue<'db> {
        &self.locals.value(level)
    }

    pub fn ty(&self, level: Level) -> &RcValue<'db> {
        &self.locals.ty(level)
    }

    pub fn push_local(&mut self, value: RcValue<'db>, ty: RcValue<'db>) {
        self.locals.push(value, ty)
    }

    pub fn push_local_var(&mut self, ty: RcValue<'db>) -> RcValue<'db> {
        self.locals.push_var(ty)
    }

    pub fn pop_local(&mut self) {
        self.locals.pop()
    }

    pub fn syn_substitution(&self) -> Vec<RcSyntax<'db>> {
        let mut substitution: Vec<RcSyntax<'db>> = Vec::new();
        for i in 0..self.depth() {
            let tm = self.value(Level(i));
            let ty = self.ty(Level(i));
            let syn_tm = self.quote(tm, ty);
            substitution.push(syn_tm);
        }
        substitution
    }

    pub fn resolve(&self, target: Name<'db>) -> Option<TypedSyntax<'db>> {
        // Try to resolve as local.
        if let Some(subject) = self.dubbing_table.resolve(target) {
            match subject {
                Dubbed::Local(level) => {
                    let index = level.to_index(self.depth());
                    let subject = Syntax::variable_rc(index);
                    let ty = self.ty(level).clone();
                    return Some(Typed(subject, ty));
                }
                Dubbed::Value(typed) => {
                    let Typed(value, ty) = typed;
                    let global_env = &self.state.borrow().global_env;
                    let depth = self.depth();
                    return Some(Typed(
                        quote::quote(global_env, depth, &*value, &*ty).unwrap(),
                        ty.clone(),
                    ));
                }
            }
        }

        // // try to resolve in current namespace, and up.
        // let resolver = Resolver::in_package(self.package);
        // resolver.resolve(self.db(), target, self.tc_env.values.global);

        // fail.
        None
    }

    pub fn poll_meta_solution(&self, meta: MetaVariableId, waker: &Waker) -> Option<RcSyntax<'db>> {
        self.state.borrow_mut().poll_meta_solution(meta, waker)
    }

    pub fn fresh_meta_id(
        &self,
        ty: RcValue<'db>,
        source_range: Option<SourceRange<'db>>,
    ) -> MetaVariableId {
        self.state.borrow_mut().fresh_meta(ty, source_range)
    }

    pub fn fresh_meta(
        &self,
        ty: RcValue<'db>,
        source_range: Option<SourceRange<'db>>,
    ) -> RcValue<'db> {
        let id = self.fresh_meta_id(ty.clone(), source_range);
        let local_env = self.locals.env().clone();
        Value::metavariable_rc(id, local_env, ty)
    }

    pub fn fresh_syn_meta(
        &self,
        ty: RcValue<'db>,
        source_range: Option<SourceRange<'db>>,
    ) -> RcSyntax<'db> {
        let id = self.fresh_meta_id(ty.clone(), source_range);
        Syntax::metavariable_rc(id, self.syn_substitution())
    }

    pub fn fresh_poisoned_meta(
        &self,
        ty: RcValue<'db>,
        source_range: Option<SourceRange<'db>>,
    ) -> RcValue<'db> {
        let id = self
            .state
            .borrow_mut()
            .fresh_poisoned_meta(ty.clone(), source_range);
        Value::metavariable_rc(id, self.local_env().clone(), ty)
    }

    pub fn meta_solution(&self, meta: MetaVariableId) -> Option<RcSyntax<'db>> {
        self.state.borrow().meta_solution(meta)
    }

    pub fn is_meta_solved(&self, meta: MetaVariableId) -> bool {
        self.state.borrow().is_meta_solved(meta)
    }

    pub fn meta_type(&self, meta: MetaVariableId) -> RcValue<'db> {
        self.state.borrow().meta_type(meta)
    }

    pub fn set_meta_solution(&self, id: MetaVariableId, solution: RcSyntax<'db>) {
        self.state.borrow_mut().set_meta_solution(id, solution);
    }

    pub fn zonk(&self, term: &Syntax<'db>) -> RcSyntax<'db> {
        crate::zonk::zonk(&self.state.borrow(), term)
    }

    pub fn quote_at_depth(
        &self,
        tm: &RcValue<'db>,
        ty: &RcValue<'db>,
        depth: usize,
    ) -> RcSyntax<'db> {
        quote::quote(&self.state.borrow().global_env, depth, tm, ty).unwrap()
    }

    pub fn quote_ty(&self, ty: &RcValue<'db>) -> RcSyntax<'db> {
        let universe = Value::universe_rc(UniverseLevel::new(0));
        self.quote(ty, &universe)
    }

    pub fn quote(&self, tm: &RcValue<'db>, ty: &RcValue<'db>) -> RcSyntax<'db> {
        self.quote_at_depth(tm, ty, self.depth())
    }

    pub fn eval(&self, tm: &RcSyntax<'db>) -> RcValue<'db> {
        let global = &self.state.borrow().global_env;
        let local = self.local_env().clone();
        let mut eval_env = val::Environment::with_locals(global, local);
        eval::eval(&mut eval_env, tm).unwrap()
    }
}

struct ReadyQueue {
    queue: RefCell<VecDeque<TaskId>>,
}

impl ReadyQueue {
    pub fn new() -> ReadyQueue {
        ReadyQueue {
            queue: RefCell::new(VecDeque::new()),
        }
    }
}

struct Task<'db> {
    future: Pin<Box<dyn Future<Output = ()> + 'db>>,
}

pub struct TaskStorage<'db> {
    tasks: RefCell<Slab<Task<'db>>>,
    ready_queue: Rc<ReadyQueue>,
}

impl<'db> TaskStorage<'db> {
    pub fn new() -> TaskStorage<'db> {
        TaskStorage {
            tasks: RefCell::new(Slab::new()),
            ready_queue: Rc::new(ReadyQueue::new()),
        }
    }

    // pub fn task(&self, task_id: usize) -> &Task {
    //     &self.tasks.borrow()[task_id]
    // }
}

#[derive(Clone)]
pub struct TaskSpawner<'db> {
    storage: Rc<TaskStorage<'db>>,
}

impl<'db> TaskSpawner<'db> {
    pub fn new(storage: Rc<TaskStorage<'db>>) -> TaskSpawner<'db> {
        TaskSpawner { storage }
    }

    pub fn spawn<F>(&self, future: F)
    where
        F: Future<Output = ()> + 'db,
    {
        let mut tasks = self.storage.tasks.borrow_mut();
        let future = Box::pin(future);
        let task = Task { future };
        let id = tasks.insert(task);
        self.storage.ready_queue.queue.borrow_mut().push_back(id);
    }
}

pub struct LocalExecutor<'db> {
    storage: Rc<TaskStorage<'db>>,
}

#[allow(unsafe_code)]
impl<'db> LocalExecutor<'db> {
    pub fn new() -> Self {
        let tasks = RefCell::new(Slab::new());
        let ready_queue = Rc::new(ReadyQueue {
            queue: RefCell::new(VecDeque::new()),
        });
        Self {
            storage: Rc::new(TaskStorage { tasks, ready_queue }),
        }
    }

    pub fn spawner(&self) -> TaskSpawner<'db> {
        TaskSpawner {
            storage: self.storage.clone(),
        }
    }

    pub fn spawn<F>(&mut self, future: F)
    where
        F: Future<Output = ()> + 'db,
    {
        let mut tasks = self.storage.tasks.borrow_mut();
        let id = tasks.insert(Task {
            future: Box::pin(future),
        });
        self.storage.ready_queue.queue.borrow_mut().push_back(id);
    }

    pub fn run(&mut self) -> Result<(), String> {
        loop {
            let task_id = self.storage.ready_queue.queue.borrow_mut().pop_front();
            let Some(task_id) = task_id else {
                break;
            };

            let waker = self.create_waker(task_id);
            let mut context = Context::from_waker(&waker);

            let mut tasks = self.storage.tasks.borrow_mut();
            if let Some(task) = tasks.get_mut(task_id) {
                match task.future.as_mut().poll(&mut context) {
                    Poll::Ready(()) => {
                        println!("[Executor] Task {} finished successfully", task_id);
                        // Only remove when done - this frees the slot for reuse
                        let _ = tasks.remove(task_id);
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
            return Err(format!(
                "Deadlock detected: {} tasks still pending but no progress can be made.\nPending tasks: {:?}\n",
                tasks.len(),
                pending_tasks,
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

pub struct WaitForResolved<'db> {
    ctx: SolverEnvironment<'db>,
    meta: MetaVariableId,
}

impl<'db> WaitForResolved<'db> {
    pub fn new(ctx: SolverEnvironment<'db>, meta: MetaVariableId) -> Self {
        WaitForResolved { ctx, meta }
    }
}

impl<'db> Future for WaitForResolved<'db> {
    type Output = RcSyntax<'db>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.ctx.poll_meta_solution(self.meta, cx.waker()) {
            Some(term) => {
                println!("[WaitForResolved] Meta {} is resolved", self.meta);
                Poll::Ready(term)
            }
            None => {
                println!("[WaitForResolved] Blocked waiting on {}", self.meta,);
                Poll::Pending
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use hwml_core::syn::Syntax;
    use hwml_core::val::Value;

    #[test]
    fn test_poisoned_meta_creation() {
        let mut state = SolverState::new();
        let ty = Value::universe_rc(hwml_core::common::UniverseLevel::new(0));
        let meta_id = state.fresh_poisoned_meta(ty, None);

        assert!(state.is_meta_poisoned(meta_id), "Meta should be poisoned");
        assert!(
            !state.is_meta_solved(meta_id),
            "Poisoned meta should not be solved"
        );
    }

    #[test]
    fn test_location_derived_ids() {
        let mut state = SolverState::new();
        let ty = Value::universe_rc(hwml_core::common::UniverseLevel::new(0));

        // Create multiple metas at the same location
        let meta1 = state.fresh_meta(ty.clone(), None);
        let meta2 = state.fresh_meta(ty.clone(), None);
        let meta3 = state.fresh_meta(ty.clone(), None);

        // They should have different local indices
        assert_ne!(meta1, meta2);
        assert_ne!(meta2, meta3);
        assert_ne!(meta1, meta3);
    }
}
