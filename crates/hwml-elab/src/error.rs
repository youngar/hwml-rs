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
