use hwml_core::{RcValue, ty::RcTy, val::{Flex, GlobalEnv}};

use crate::{error::ElabError, state::SolverState};

/// Attempt Miller pattern unification: `Flex { id, local, spine } = rhs`.
///
/// 1. Collect distinct variable levels from local env + spine.
/// 2. Build inverse renaming: level → meta-internal index.
/// 3. Scope-check and rename RHS.
/// 4. Solve the meta.
///
/// Returns `Ok(true)` on success, `Ok(false)` if not a pattern (non-linear or rhs out-of-scope).
pub fn pattern_unify<'db>(
    _global: &GlobalEnv<'db>,
    _state: &mut SolverState<'db>,
    _flex: &Flex<'db>,
    _rhs: RcValue<'db>,
    _rhs_ty: RcTy<'db>,
) -> Result<bool, ElabError<'db>> {
    todo!("pattern_unify: Phase 2")
}
