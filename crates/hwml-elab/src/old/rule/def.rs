// use hwml_core::*;
// use crate::*;

// /// `def foo telescope := bar`
// pub struct DefRule<'db> {
//   location: Option<Range<usize>>,
// 	problem: ElabProblem<'db>,
// 	body: ElabTerm<'db>,
// }

// impl ElabDecl for DefRule<'db> {
//   async fn elab_decl(&self, env: ElabEnv<'db>) -> ElabResult<'db, ()> {
//     let iproblem = try await self.problem.elab_problem(env)
//     let defType = try await ensure_claim(env, problem: iproblem)
//     let vtype = await env.evaluator().evaluate(type: defType)

//     var rhsEnv = env.restricting_toplevel_env(before: iproblem.name)
//     rhsEnv.namespace = iproblem.names

//     let tactic = ElabTactics.lambdas(provenance: self.provenance, binders: iproblem.untyped_binders[...]) {
//       Return(provenance: self.provenance) { self.body }
//     }

//     let term = await tactic.recover_elab_term(rhsEnv, type: vtype)

//     let emission = Emission(def: GlobalDef(type: defType, term: term, cause: .userHole))
//     await env.sink.emit(name: iproblem.name, emission)
//   }
// }
// pub fn elab_def<'db>(
//     env: ElabEnv<'db>,
//     name: Name<'db>,
//     params: Vec<(Name<'db>, SyntaxTactic<'db>)>,
//     ty: SyntaxTactic<'db>,
//     body: SyntaxTactic<'db>,
// ) -> ElabResult<'db, ()> {

//   	struct Define: ElabDecl, HasProvenance {
// 		let provenance: Range<Int>?
// 		let problem: ElabProblem
// 		let body: ElabTerm

// 		func elabDecl(_ env: ElabEnv) async throws(ElabError) {
// 			let iproblem = try await problem.elabProblem(env)
// 			let defType = try await ensureClaim(env, problem: iproblem)
// 			let vtype = await env.evaluator().evaluate(type: defType)

// 			var rhsEnv = env.restrictingToplevelEnv(before: iproblem.name)
// 			rhsEnv.namespace = iproblem.names

// 			let tactic = ElabTactics.lambdas(provenance: provenance, binders: iproblem.untypedBinders[...]) {
// 				Return(provenance: provenance) { body }
// 			}

// 			let term = await tactic.recoverElabTerm(rhsEnv, type: vtype)

// 			let emission = Emission(def: GlobalDef(type: defType, term: term, cause: .userHole))
// 			await env.sink.emit(name: iproblem.name, emission)
// 		}
// 	}

// }
