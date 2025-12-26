use std::collections::HashMap;

use crate::Constraint;
use hwml_core::common::*;
use hwml_core::syn::basic::*;
use hwml_core::syn::{Closure, ConstantId};

/// A custom environment for the elaborator that tracks types and provides
/// the methods needed for context manipulation.
#[derive(Clone, Debug)]
pub struct ElabEnvironment<'db> {
    types: Vec<RcSyntax<'db>>,
}

impl<'db> ElabEnvironment<'db> {
    pub fn new() -> Self {
        ElabEnvironment { types: Vec::new() }
    }

    pub fn depth(&self) -> usize {
        self.types.len()
    }

    pub fn extend(&mut self, ty: RcSyntax<'db>) -> Level {
        let level = Level::new(self.types.len());
        self.types.push(ty);
        level
    }

    pub fn lookup(&self, level: Level) -> RcSyntax<'db> {
        let index: usize = level.into();
        self.types[index].clone()
    }

    pub fn to_index(&self, level: Level) -> Index {
        level.to_index(self.depth())
    }

    pub fn pop(&mut self) {
        self.types.pop();
    }

    pub fn truncate(&mut self, depth: usize) {
        self.types.truncate(depth);
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub enum NameKind<'db> {
    Local(Level),
    Global(ConstantId<'db>),
}

pub struct NameMap {
    pub names: Vec<Box<[u8]>>,
}

impl NameMap {
    pub fn new() -> NameMap {
        NameMap { names: Vec::new() }
    }

    pub fn lookup(&self, name: &Box<[u8]>) -> Option<Level> {
        self.names
            .iter()
            .rposition(|n| *n == *name)
            .map(|pos| Level::new(pos))
    }

    pub fn push(&mut self, name: Box<[u8]>) {
        self.names.push(name);
    }

    pub fn pop(&mut self) {
        self.names.pop();
    }
}

pub struct State<'db> {
    pub constraints: Vec<Constraint<'db>>,
    closure: Closure<'db>,
    env: ElabEnvironment<'db>,
    name_map: NameMap,
    solved_metas: HashMap<MetaVariableId, RcSyntax<'db>>,
    next_metavariable_id: usize,
}

impl<'db> State<'db> {
    pub fn new() -> State<'db> {
        State {
            constraints: Vec::new(),
            closure: Closure::new(),
            env: ElabEnvironment::new(),
            name_map: NameMap::new(),
            solved_metas: HashMap::new(),
            next_metavariable_id: 0,
        }
    }

    pub fn depth(&self) -> usize {
        self.env.depth()
    }

    pub fn extend_context_nameless(&mut self, ty: RcSyntax<'db>) -> Level {
        let level = self.env.extend(ty);
        let index = self.level_to_index(level);
        // TODO: we assume that we are going underneath a binder - this is not
        // always true (maybe for let-in constructs we should push the
        // referenced value).
        self.closure.values.push(Syntax::variable_rc(index));
        level
    }

    pub fn extend_context(&mut self, name: Box<[u8]>, ty: RcSyntax<'db>) -> Level {
        let level = self.extend_context_nameless(ty);
        self.name_map.push(name);
        level
    }

    pub fn pop_context(&mut self) {
        self.env.pop();
        self.closure.pop();
    }

    pub fn truncate_context(&mut self, depth: usize) {
        self.env.truncate(depth);
        self.closure.truncate(depth);
    }

    pub fn context(&self) -> Closure<'db> {
        self.closure.clone()
    }

    pub fn lookup_local(&self, name: &Box<[u8]>) -> Option<Level> {
        self.name_map.lookup(name)
    }

    pub fn lookup_local_type(&self, name: &Box<[u8]>) -> Option<RcSyntax<'db>> {
        self.name_map
            .lookup(name)
            .map(|level| self.env.lookup(level))
    }

    pub fn lookup_global_type(&self, _name: Box<[u8]>) -> RcSyntax<'db> {
        todo!()
    }

    pub fn level_to_index(&self, level: Level) -> Index {
        self.env.to_index(level)
    }

    pub fn type_of(&self, level: Level) -> RcSyntax<'db> {
        self.env.lookup(level)
    }

    pub fn fresh_metavariable_id(&mut self) -> MetaVariableId {
        let id = MetaVariableId(self.next_metavariable_id);
        self.next_metavariable_id += 1;
        id
    }

    pub fn solve_metavariable_id(&mut self, meta: MetaVariableId, tm: RcSyntax<'db>) {
        assert!(!self.solved_metas.contains_key(&meta));
        self.solved_metas.insert(meta, tm);
    }

    /// Create a new metavariable under the current context.
    pub fn metavariable(&mut self, id: MetaVariableId) -> RcSyntax<'db> {
        Syntax::metavariable_rc(id, self.closure.values.clone())
    }

    /// Create a fresh metavariable under the current context.
    pub fn fresh_metavariable(&mut self) -> RcSyntax<'db> {
        let id = self.fresh_metavariable_id();
        self.metavariable(id)
    }

    pub fn solve_metavariable(&mut self, meta: Metavariable<'db>, tm: RcSyntax<'db>) {
        self.solve_metavariable_id(meta.id, tm);
    }

    pub fn register_constraint(&mut self, constraint: Constraint<'db>) {
        self.constraints.push(constraint);
    }

    pub fn equality_constraint(
        &mut self,
        lhs: RcSyntax<'db>,
        rhs: RcSyntax<'db>,
        ty: RcSyntax<'db>,
    ) -> MetaVariableId {
        let antiunifier = self.fresh_metavariable_id();
        let constraint = Constraint::equality(lhs, rhs, ty, antiunifier);
        self.register_constraint(constraint);
        antiunifier
    }
}
