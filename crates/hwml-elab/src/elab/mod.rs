pub mod decl;
pub mod expr;

use hwml_core::{RcSyntax, ty::RcTy, val::GlobalEnv};
use hwml_surface::Expression;

use crate::{
    ctx::ElabCtx,
    error::ElabError,
    kernel::{Checked, Kernel},
    state::SolverState,
};

pub struct Elaborator<'a, 'db> {
    pub kernel: Kernel<'a, 'db>,
}

impl<'a, 'db> Elaborator<'a, 'db> {
    pub fn new(
        global: &'a GlobalEnv<'db>,
        ctx: ElabCtx<'db>,
        state: &'a mut SolverState<'db>,
    ) -> Self {
        Elaborator { kernel: Kernel::new(global, ctx, state) }
    }

    pub fn new_with_names(
        global: &'a GlobalEnv<'db>,
        ctx: ElabCtx<'db>,
        state: &'a mut SolverState<'db>,
        global_names: crate::names::RcGlobalNameTable<'db>,
    ) -> Self {
        Elaborator { kernel: Kernel::new_with_names(global, ctx, state, global_names) }
    }

    /// Pull-mode: infer (term, type).
    pub fn synth(
        &mut self,
        expr: &Expression,
    ) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
        expr::synth(self, expr)
    }

    /// Push-mode: check against expected type.
    /// Always returns a term of exactly `expected_ty` (via `expect` pattern).
    pub fn check(
        &mut self,
        expr: &Expression,
        expected_ty: RcTy<'db>,
    ) -> Result<Checked<RcSyntax<'db>>, ElabError<'db>> {
        expr::check(self, expr, expected_ty)
    }

    /// Extend context under a Pi binder, run `f`, then restore.
    ///
    /// `ty` = semantic type for the context entry.
    /// `ty_code` = value-level type code for the rigid neutral's annotation.
    pub fn under_binder<R>(
        &mut self,
        name: String,
        ty: RcTy<'db>,
        ty_code: hwml_core::RcValue<'db>,
        f: impl FnOnce(&mut Elaborator<'a, 'db>, hwml_core::RcValue) -> R,
    ) -> R {
        let var = self.kernel.ctx.fresh_var(ty_code);
        let new_ctx = self.kernel.ctx.push_bound(name, ty, var.clone());
        let old_ctx = std::mem::replace(&mut self.kernel.ctx, new_ctx);
        let result = f(self, var);
        self.kernel.ctx = old_ctx;
        result
    }
}
