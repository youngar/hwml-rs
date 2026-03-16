use crate::*;
use hwml_core::*;
use refiner::env::Env;

// pub trait ElabSyntax<'db> {
//     async fn elab_syntax(&self, env: Env<'db>, ty: RcValue<'db>) -> RcSyntax<'db>;
// }

// pub trait ElabTypedSyntax<'db> {
//     async fn elab_typed_syntax(&self, env: Env<'db>) -> TypedSyntax<'db>;
// }

// /// Elaborator for Pi's.
// struct PiRule<'db> {
//     source: Box<SyntaxTactic<'db>>,
//     target: Box<SyntaxTactic<'db>>,
// }

// type ElabSyntax<'db> = ElabResult<'db, RcSyntax<'db>>;

// async fn elab_pi(source: Future<ElabSyntax<'db>>, target: Future<ElabSyntax<'db>>) -> ElabSyntax<'db> {
//   // ....
// }

// impl<'db> PiRule<'db> {
//   pub fn new(syntax)
// }

// impl<'db> ElabSyntax<'db> for PiRule<'db> {
//     async fn elab_syntax(&self, env: Env<'db>) -> RcSyntax<'db> {
//         let source_env = env.enter_subgloal("dom");
//         let dom = self.dom.elab_type(dom_env).await;

//         let cod_env = env.enter_subgoal("cod");
//         env_cod.bind(None, dom).await;

//         let cod = self.cod.elab_type(env_cod).await;

//         Ok(Syntax::pi_rc(source, target))
//     }
// }
