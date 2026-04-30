use crate::{error::ElabError, state::SolverState};

/// Universe meta zonking pass.
///
/// After the solver reaches a fixed point:
/// 1. For each unsolved `MetaKind::UniverseLevel` meta:
///    compute minimum bound from `LevelLeq` constraints; default to 0.
/// 2. For remaining unsolved metas: report `ElabError::UnsolvedMeta`.
pub fn zonk<'db>(_state: &mut SolverState<'db>) -> Result<(), ElabError<'db>> {
    todo!("zonk: Phase 3")
}
