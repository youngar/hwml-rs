use hwml_core::val::GlobalEnv;

use crate::{error::ElabError, state::SolverState};

pub struct Solver<'a, 'db> {
    pub state: &'a mut SolverState<'db>,
    pub global: &'db GlobalEnv<'db>,
}

#[derive(Debug)]
pub enum SolveError<'db> {
    Elab(ElabError<'db>),
    NoProgress,
}

impl<'a, 'db> Solver<'a, 'db> {
    pub fn new(state: &'a mut SolverState<'db>, global: &'db GlobalEnv<'db>) -> Self {
        Solver { state, global }
    }

    /// Run flat constraint solver until queue empty or no progress.
    ///
    /// Ordered plugins (each a function, no extensibility needed):
    /// 1. propagate — substitute solved Flex heads
    /// 2. reduce — WHNF-reduce both sides
    /// 3. identity — definitionally equal → mark Solved
    /// 4. het_reduce — HetEq with equal types → homogeneous
    /// 5. left_meta — lhs unsolved Flex → pattern_unify
    /// 6. right_meta — rhs unsolved Flex → pattern_unify
    /// 7. pi_injectivity — PiCode(A,B) = PiCode(A',B') → split
    /// 8. constructor_injectivity — same ctor → split
    /// 9. level_leq — LevelLeq → propagate bound to meta
    /// 10. block — none above → compute blocking metas
    pub fn run(&mut self) -> Result<(), SolveError<'db>> {
        todo!("Solver::run: Phase 3")
    }
}
