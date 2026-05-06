use hwml_core::{ty::RcTy, RcValue, SourceRange};

use crate::meta::MetaId;

#[derive(Debug, Clone)]
pub enum ElabError<'db> {
    TypeMismatch {
        expected: RcTy<'db>,
        actual: RcTy<'db>,
        span: Option<SourceRange<'db>>,
    },
    NotInScope {
        name: String,
        span: Option<SourceRange<'db>>,
    },
    CannotInfer {
        span: Option<SourceRange<'db>>,
    },
    UnificationFailure {
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
        span: Option<SourceRange<'db>>,
    },
    OccursCheck {
        meta: MetaId,
        span: Option<SourceRange<'db>>,
    },
    ScopeViolation {
        meta: MetaId,
        span: Option<SourceRange<'db>>,
    },
    UnsolvedMeta {
        meta: MetaId,
        span: Option<SourceRange<'db>>,
    },
    MetaAlreadySolved {
        meta: MetaId,
    },
    NotImplemented {
        feature: String,
        span: Option<SourceRange<'db>>,
    },
}

// NOTE: Salsa accumulators are the proper way to collect diagnostics in tracked functions.
// However, `elab_library_with_sccs` cannot currently be a `#[salsa::tracked]` function
// because it takes `&mut GlobalEnv` as a parameter. Salsa tracked functions must be pure
// and cannot take mutable references.
//
// For now, we use the simpler pattern of returning `Vec<ElabError>` in `ElabProgramResult`.
// The elaboration loop is lenient: it catches errors, pushes them to the Vec, and continues
// processing the rest of the library instead of short-circuiting.
//
// Future refactoring could make elaboration a proper tracked function by having it return
// a new GlobalEnv instead of mutating an existing one. Then we could use Salsa accumulators:
//
// ```rust
// #[salsa::accumulator]
// pub struct ElabDiagnostics(pub ElabError);
//
// #[salsa::tracked]
// pub fn elab_library_tracked(db: &dyn Database, ...) -> GlobalEnv {
//     // Push errors using ElabDiagnostics::push(db, error)
//     // Retrieve using ElabDiagnostics::accumulated(db, ...)
// }
// ```
