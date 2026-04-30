use hwml_core::{RcSyntax, ty::RcTy, val::GlobalEnv};
use hwml_surface::Expression;

use crate::{ctx::ElabCtx, error::ElabError, meta::MetaId, state::SolverState};

/// Zero-cost proof a term was built by a kernel typing rule.
/// `new` is `pub(crate)` — only this module can construct `Checked` values.
pub struct Checked<T>(T);

impl<T> Checked<T> {
    pub(crate) fn new(v: T) -> Self {
        Checked(v)
    }

    pub fn into_inner(self) -> T {
        self.0
    }
}

pub struct Kernel<'a, 'db> {
    pub global: &'db GlobalEnv<'db>,
    pub ctx: ElabCtx<'db>,
    pub state: &'a mut SolverState<'db>,
}

impl<'a, 'db> Kernel<'a, 'db> {
    pub fn new(
        global: &'db GlobalEnv<'db>,
        ctx: ElabCtx<'db>,
        state: &'a mut SolverState<'db>,
    ) -> Self {
        Kernel { global, ctx, state }
    }

    /// Check a lambda body under a Pi type.
    pub fn check_lambda(
        &mut self,
        _bindings: &hwml_surface::Bindings,
        _body: &Expression,
        _dom: RcTy<'db>,
        _cod: std::rc::Rc<hwml_core::ty::TyClosure<'db>>,
    ) -> Result<Checked<RcSyntax<'db>>, ElabError<'db>> {
        todo!("check_lambda: Phase 2")
    }

    /// Synthesize a variable from a de Bruijn index.
    pub fn synth_var(
        &self,
        idx: hwml_core::Index,
    ) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
        todo!("synth_var: Phase 2")
    }

    /// Synthesize an application: function already checked, check arg against domain.
    pub fn synth_app(
        &mut self,
        fun: Checked<(RcSyntax<'db>, RcTy<'db>)>,
        arg: &Expression,
    ) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
        todo!("synth_app: Phase 2")
    }

    /// Synthesize a metavariable applied to all current context variables.
    pub fn synth_meta(
        &mut self,
        id: MetaId,
    ) -> Checked<(RcSyntax<'db>, RcTy<'db>)> {
        todo!("synth_meta: Phase 2")
    }

    /// Synthesize the `Type` keyword with optional universe level hint.
    /// McBride/Sterling: no hint → fresh `?u : UniverseType`.
    pub fn synth_universe(
        &mut self,
        hint: Option<usize>,
    ) -> Checked<(RcSyntax<'db>, RcTy<'db>)> {
        todo!("synth_universe: Phase 2")
    }

    /// The tog `expect` primitive.
    ///
    /// Always returns a term of exactly `expected_ty`.
    /// Fast path: if types syntactically equal, return rhs directly.
    /// Slow path: create meta `t:expected_ty`, emit HetEq(t:expected_ty, rhs:actual_ty).
    pub fn expect(
        &mut self,
        expected_ty: RcTy<'db>,
        rhs: Checked<(RcSyntax<'db>, RcTy<'db>)>,
    ) -> Checked<RcSyntax<'db>> {
        todo!("expect: Phase 2")
    }
}
