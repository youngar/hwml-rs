use crate::elaborator::{ElabResult, ElabEnv};
use crate::*;

use hwml_core::*;

pub trait ElabRule<'db> {
    async fn elab_rule(&self, env: ElabEnv<'db>) -> ElabResult<'db, Trust<RcSyntax<'db>>>;
}

pub trait DeclElaborator<'db> {
    async fn elab_decl(&self, env: ElabEnv<'db>) -> ElabResult<'db, ()>;
}

pub trait ProblemElaborator<'db> {
    async fn elab_problem(&self, env: ElabEnv<'db>) -> ElabResult<'db, ElabProblem>;
}

type ElabProblem<'db> = Future<ElabResult<'db, ElabProblem<'db>>>;

pub mod def;

pub use def::*;
