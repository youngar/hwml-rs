pub mod decl;
pub mod expr;

use hwml_core::{ty::RcTy, val::GlobalEnv, RcSyntax, Source, SourceRange};
use hwml_surface::Expression;

use crate::{
    context::ElabContext,
    ctx::ElabCtx,
    error::ElabError,
    kernel::{Checked, Kernel},
    resolver::Resolver,
    state::SolverState,
    stub_table::StubTable,
};

pub struct Elaborator<'a, 'db> {
    pub kernel: Kernel<'a, 'db>,
    pub context: ElabContext<'db>,
}

impl<'a, 'db> Elaborator<'a, 'db> {
    pub fn new(
        global: &'a GlobalEnv<'db>,
        ctx: ElabCtx<'db>,
        state: &'a mut SolverState<'db>,
        resolver: &'a Resolver<'db>,
        stub_table: &'a StubTable<'db>,
        source: Source<'db>,
    ) -> Self {
        Elaborator {
            kernel: Kernel::new(global, ctx, state, resolver, stub_table),
            context: ElabContext::new(source),
        }
    }

    /// Create an elaborator preserving an existing elaboration context.
    ///
    /// This is used when creating nested elaborators during elaboration to preserve
    /// the backtrace stack.
    pub fn with_context(
        global: &'a GlobalEnv<'db>,
        ctx: ElabCtx<'db>,
        state: &'a mut SolverState<'db>,
        resolver: &'a Resolver<'db>,
        stub_table: &'a StubTable<'db>,
        elab_context: ElabContext<'db>,
    ) -> Self {
        Elaborator {
            kernel: Kernel::new(global, ctx, state, resolver, stub_table),
            context: elab_context,
        }
    }

    // ===== Phase 4.2: Error Construction Helpers =====
    // These helpers automatically capture the elaboration backtrace

    /// Create a TypeMismatch error with automatic backtrace capture
    pub fn error_type_mismatch(
        &self,
        expected: hwml_core::ty::RcTy<'db>,
        actual: hwml_core::ty::RcTy<'db>,
        span: Option<SourceRange<'db>>,
    ) -> ElabError<'db> {
        ElabError::TypeMismatch {
            expected,
            actual,
            span,
            elab_backtrace: self.context.snapshot(),
        }
    }

    /// Create a NotInScope error with automatic backtrace capture
    pub fn error_not_in_scope(
        &self,
        name: String,
        span: Option<SourceRange<'db>>,
    ) -> ElabError<'db> {
        ElabError::NotInScope {
            name,
            span,
            elab_backtrace: self.context.snapshot(),
        }
    }

    /// Create a CannotInfer error with automatic backtrace capture
    pub fn error_cannot_infer(&self, span: Option<SourceRange<'db>>) -> ElabError<'db> {
        ElabError::CannotInfer {
            span,
            elab_backtrace: self.context.snapshot(),
        }
    }

    /// Create a NotImplemented error with automatic backtrace capture
    pub fn error_not_implemented(
        &self,
        feature: String,
        span: Option<SourceRange<'db>>,
    ) -> ElabError<'db> {
        ElabError::NotImplemented {
            feature,
            span,
            elab_backtrace: self.context.snapshot(),
        }
    }

    // ===== Elaboration Methods =====

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

    /// Helper to push a trace frame.
    ///
    /// Note: You MUST call `pop_trace()` when done, or use manual scoping
    /// carefully to ensure cleanup on all paths (including errors).
    ///
    /// For most cases, it's better to structure code so traces are pushed/popped
    /// in simple, non-early-returning blocks.
    pub fn push_trace(
        &mut self,
        desc: impl Into<String>,
        byte_range: std::ops::Range<usize>,
        kind: crate::context::ElabFrameKind,
    ) {
        self.context.push_trace(desc, byte_range, kind);
    }

    /// Pop the most recent trace frame.
    pub fn pop_trace(&mut self) {
        self.context.pop_trace();
    }
}
