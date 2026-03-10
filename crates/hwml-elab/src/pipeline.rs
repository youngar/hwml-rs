//! End-to-end elaboration pipeline from surface syntax to core IR.

use hwml_core::check::TCEnvironment;
use hwml_core::syn::Syntax;
use hwml_core::val::{Environment, GlobalEnv};
use hwml_support::SourceFile;
use hwml_surface::syntax as surface;
use std::rc::Rc;

use crate::elaborator::{synth, Diagnostic, ElaborationContext};
use crate::engine::{SingleThreadedExecutor, SolverEnvironment};

pub struct ElaborationResult<'db> {
    pub term: Option<Rc<Syntax<'db>>>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn elaborate_expression<'db>(
    db: &'db dyn salsa::Database,
    source_file: SourceFile,
    expr: &surface::Expression,
) -> ElaborationResult<'db> {
    let global_env = GlobalEnv::new();
    let executor = SingleThreadedExecutor::new();
    let spawner = executor.spawner();

    let tc_env = TCEnvironment {
        db,
        values: Environment::new(&global_env),
        types: Vec::new(),
    };

    let solver = SolverEnvironment::new(tc_env, spawner);
    let mut ctx = ElaborationContext::new(db, Some(source_file), solver);

    let (term, _ty) = futures::executor::block_on(async { synth(&mut ctx, expr).await });

    ElaborationResult {
        term: Some(term),
        diagnostics: ctx.diagnostics().to_vec(),
    }
}

pub fn elaborate_program<'db>(
    db: &'db dyn salsa::Database,
    source_file: SourceFile,
    program: &surface::Program,
) -> Vec<ElaborationResult<'db>> {
    program
        .statements
        .iter()
        .map(|statement| match statement {
            surface::Statement::Def(def) => &def.value,
            surface::Statement::Meta(meta) => &meta.value,
        })
        .map(|expr| elaborate_expression(db, source_file, expr))
        .collect()
}
