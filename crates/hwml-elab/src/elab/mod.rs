pub mod decl;
pub mod expr;

use hwml_core::{ty::RcTy, val::GlobalEnv, RcSyntax};
use hwml_surface::Expression;

use crate::{
    ctx::ElabCtx,
    error::ElabError,
    kernel::{Checked, Kernel},
    resolver::Resolver,
    state::SolverState,
    stub_table::StubTable,
};

pub struct Elaborator<'a, 'db> {
    pub kernel: Kernel<'a, 'db>,
}

impl<'a, 'db> Elaborator<'a, 'db> {
    pub fn new(
        global: &'a GlobalEnv<'db>,
        ctx: ElabCtx<'db>,
        state: &'a mut SolverState<'db>,
        resolver: &'a Resolver<'db>,
        stub_table: &'a StubTable<'db>,
    ) -> Self {
        Elaborator {
            kernel: Kernel::new(global, ctx, state, resolver, stub_table),
        }
    }

    /// Pull-mode: infer (term, type).
    pub fn synth<Db>(
        &mut self,
        db: &'db Db,
        expr: &Expression,
    ) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
    where
        Db: salsa::Database,
    {
        expr::synth(db, self, expr)
    }

    /// Push-mode: check against expected type.
    /// Always returns a term of exactly `expected_ty` (via `expect` pattern).
    pub fn check<Db>(
        &mut self,
        db: &'db Db,
        expr: &Expression,
        expected_ty: RcTy<'db>,
    ) -> Result<Checked<RcSyntax<'db>>, ElabError<'db>>
    where
        Db: salsa::Database,
    {
        expr::check(db, self, expr, expected_ty)
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
