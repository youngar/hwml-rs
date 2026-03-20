use crate::*;
use hwml_core::*;

pub fn switch<'db, 'g, F>(
    env: SolverEnvironment<'db, 'g>,
    loc: Option<SourceRange<'db>>,
    lhs_ty: RcValue<'db>,
    f: F,
) -> TrustedSyntax<'db>
where
    F: FnOnce(SolverEnvironment<'db, 'g>) -> TrustedTypedSyntax<'db>,
{
    let sem_lhs = env.fresh_meta(lhs_ty.clone(), None);
    let syn_lhs = env.quote(&sem_lhs, &lhs_ty);
    let Trusted(Typed(syn_rhs, rhs_ty)) = f(env.clone());
    let sem_rhs = env.eval(&syn_rhs);
    let bg = env.clone();
    env.constrain(async move {
        unify_ty(bg.clone(), lhs_ty.clone(), rhs_ty).await.unwrap();
        unify(bg.db(), bg, sem_lhs, sem_rhs, lhs_ty).await.unwrap();
    });
    Trusted(syn_lhs)
}
