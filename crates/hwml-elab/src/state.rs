use std::collections::HashMap;

use crate::Constraint;
use hwml_core::common::*;
use hwml_core::syn::basic::*;
use hwml_core::syn::{Closure, Environment, NameId};

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub enum NameKind {
    Local(Level),
    Global(NameId),
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

pub struct State {
    pub constraints: Vec<Constraint>,
    closure: Closure,
    env: Environment,
    name_map: NameMap,
    solved_metas: HashMap<MetavariableId, RcSyntax>,
}

impl State {
    pub fn new() -> State {
        State {
            constraints: Vec::new(),
            closure: Closure::new(),
            env: Environment::new(),
            name_map: NameMap::new(),
            solved_metas: HashMap::new(),
        }
    }

    pub fn depth(&self) -> usize {
        self.env.depth()
    }

    pub fn extend_context_nameless(&mut self, ty: RcSyntax) -> Level {
        let level = self.env.extend(ty);
        let index = self.level_to_index(level);
        // TODO: we assume that we are going underneath a binder - this is not
        // always true (maybe for let-in constructs we should push the
        // referenced value).
        self.closure.values.push(Syntax::variable_rc(index));
        level
    }

    pub fn extend_context(&mut self, name: Box<[u8]>, ty: RcSyntax) -> Level {
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

    pub fn context(&self) -> Closure {
        self.closure.clone()
    }

    pub fn lookup_local(&self, name: &Box<[u8]>) -> Option<Level> {
        self.name_map.lookup(name)
    }

    pub fn lookup_local_type(&self, name: &Box<[u8]>) -> Option<RcSyntax> {
        self.name_map
            .lookup(name)
            .map(|level| self.env.lookup(level))
    }

    pub fn lookup_global_type(&self, name: Box<[u8]>) -> RcSyntax {
        todo!()
    }

    pub fn level_to_index(&self, level: Level) -> Index {
        self.env.to_index(level)
    }

    pub fn type_of(&self, level: Level) -> RcSyntax {
        self.env.lookup(level)
    }

    pub fn fresh_metavariable_id(&self) -> MetavariableId {
        MetavariableId::new(MetavariableData::new())
    }

    pub fn solve_metavariable_id(&mut self, meta: MetavariableId, tm: RcSyntax) {
        assert!(!self.solved_metas.contains_key(&meta));
        self.solved_metas.insert(meta, tm);
    }

    /// Create a new metavariable under the current context.
    pub fn metavariable(&self, id: MetavariableId) -> RcSyntax {
        Syntax::metavariable_rc(id, self.closure.clone())
    }

    /// Create a fresh metavariable under the current context.
    pub fn fresh_metavariable(&self) -> RcSyntax {
        self.metavariable(self.fresh_metavariable_id())
    }

    pub fn solve_metavariable(&mut self, meta: Metavariable, tm: RcSyntax) {
        self.solve_metavariable_id(meta.id, tm);
    }

    pub fn register_constraint(&mut self, constraint: Constraint) {
        self.constraints.push(constraint);
    }

    pub fn equality_constraint(
        &mut self,
        lhs: RcSyntax,
        rhs: RcSyntax,
        ty: RcSyntax,
    ) -> MetavariableId {
        let antiunifier = self.fresh_metavariable_id();
        let constraint = Constraint::equality(lhs, rhs, ty, antiunifier.clone());
        self.register_constraint(constraint);
        antiunifier
    }
}
