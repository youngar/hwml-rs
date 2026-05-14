use hwml_core::{
    ty::RcTy,
    val::{LocalEnv, TransparentEnv},
    Index, Level, RcValue, Value,
};
use im::Vector;

#[derive(Debug, Clone)]
pub enum Binding<'db> {
    /// Regular lambda or Pi binding.
    Bound,
    /// Let binding: the value is transparent during conversion checking.
    Let(RcValue<'db>),
}

#[derive(Debug, Clone)]
pub struct CtxEntry<'db> {
    pub name: String,
    pub ty: RcTy<'db>,
    /// The runtime value for this binding: a rigid neutral for `Bound`,
    /// the let-value itself for `Let`.
    pub value: RcValue<'db>,
    pub binding: Binding<'db>,
}

/// Local elaboration context. Uses `im::Vector` so `push_*` costs O(log n)
/// but `.clone()` costs O(1) — safe to clone at each binder when descending.
#[derive(Debug, Clone)]
pub struct ElabCtx<'db> {
    entries: Vector<CtxEntry<'db>>,
}

impl<'db> Default for ElabCtx<'db> {
    fn default() -> Self {
        Self::empty()
    }
}

impl<'db> ElabCtx<'db> {
    pub fn empty() -> Self {
        ElabCtx {
            entries: Vector::new(),
        }
    }

    pub fn depth(&self) -> usize {
        self.entries.len()
    }

    /// Extend with a bound variable (opaque). `val` should be a rigid neutral
    /// at the current depth — callers create it with `Value::variable_rc`.
    pub fn push_bound(&self, name: String, ty: RcTy<'db>, val: RcValue<'db>) -> Self {
        let mut new = self.clone();
        new.entries.push_back(CtxEntry {
            name,
            ty,
            value: val,
            binding: Binding::Bound,
        });
        new
    }

    /// Extend with a let binding (transparent value).
    pub fn push_let(&self, name: String, ty: RcTy<'db>, val: RcValue<'db>) -> Self {
        let mut new = self.clone();
        new.entries.push_back(CtxEntry {
            name,
            ty,
            value: val.clone(),
            binding: Binding::Let(val),
        });
        new
    }

    /// Look up a name and return its de Bruijn index and entry.
    /// Searches from innermost (highest index) to outermost.
    pub fn lookup(&self, name: &str) -> Option<(Index, &CtxEntry<'db>)> {
        let depth = self.entries.len();
        for (i, entry) in self.entries.iter().enumerate().rev() {
            if entry.name == name {
                // i is the level (0 = outermost); convert to index
                let index = Index::new(depth - 1 - i);
                return Some((index, entry));
            }
        }
        None
    }

    /// Look up a binding by de Bruijn level (0 = outermost).
    pub fn lookup_level(&self, level: Level) -> Option<&CtxEntry<'db>> {
        self.entries.get(level.0)
    }

    /// Build a `LocalEnv` from this context (for use with `eval`).
    pub fn to_local_env(&self) -> LocalEnv<'db> {
        let mut env = LocalEnv::new();
        for entry in self.entries.iter() {
            env.push(entry.value.clone());
        }
        env
    }

    /// Build a `TransparentEnv` from this context (for use with `equate`).
    pub fn to_transparent_env(&self) -> TransparentEnv<'db> {
        let mut env = TransparentEnv::new();
        for entry in self.entries.iter() {
            match &entry.binding {
                Binding::Bound => env.push_rigid(),
                Binding::Let(val) => env.push_transparent(val.clone()),
            }
        }
        env
    }

    /// Iterate entries from outermost to innermost.
    pub fn iter(&self) -> impl Iterator<Item = &CtxEntry<'db>> {
        self.entries.iter()
    }

    /// Fresh rigid variable at the current depth, suitable for `push_bound`.
    pub fn fresh_var(&self, ty: RcValue<'db>) -> RcValue<'db> {
        Value::variable_rc(Level::new(self.depth()), ty)
    }
}
