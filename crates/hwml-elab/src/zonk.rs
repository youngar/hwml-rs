use std::rc::Rc;

use hwml_core::{RcSyntax, RcValue, Syntax, Value};

use crate::{
    constraint::Constraint,
    error::ElabError,
    meta::{MetaId, MetaKind},
    state::SolverState,
};

/// Universe meta zonking pass.
///
/// After the solver reaches a fixed point:
/// 1. Collect minimum bounds for each UniverseLevel meta from LevelLeq constraints.
/// 2. Solve all unsolved UniverseLevel metas (default to level 0).
/// 3. Report any remaining unsolved Term metas as errors.
pub fn zonk<'db>(state: &mut SolverState<'db>) -> Result<(), ElabError<'db>> {
    let mut min_bounds: std::collections::HashMap<MetaId, usize> =
        std::collections::HashMap::new();

    let cids: Vec<_> = state.iter_constraints().map(|(id, _)| *id).collect();
    for cid in cids {
        let entry = state.constraint(cid).unwrap().clone();
        if let Constraint::LevelLeq { smaller, larger } = &entry.constraint {
            if let (Value::UniverseCode(n), Value::Flex(flex)) =
                (smaller.as_ref(), larger.as_ref())
            {
                let id = MetaId(flex.head.id.local_index as u32);
                let bound = min_bounds.entry(id).or_insert(0);
                if *n > *bound {
                    *bound = *n;
                }
            }
        }
    }

    let universe_metas: Vec<MetaId> = state
        .iter_metas()
        .filter_map(|(id, entry)| {
            if matches!(entry.kind, MetaKind::UniverseLevel) && entry.solution.is_none() {
                Some(*id)
            } else {
                None
            }
        })
        .collect();

    for id in universe_metas {
        let level = min_bounds.get(&id).copied().unwrap_or(0);
        let syn: RcSyntax<'db> = Rc::new(Syntax::UniverseCode(level));
        let val: RcValue<'db> = Rc::new(Value::UniverseCode(level));
        state.solve_meta(id, syn, val)?;
    }

    for (id, entry) in state.iter_metas() {
        if entry.solution.is_none() {
            return Err(ElabError::UnsolvedMeta { meta: *id, span: None });
        }
    }

    Ok(())
}
