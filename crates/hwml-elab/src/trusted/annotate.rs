use crate::*;
use hwml_core::*;

pub fn annotate<'db, 'g, F>(
    env: SolverEnvironment<'db, 'g>,
    lhs_ty: RcValue<'db>,
    f: F,
) -> TrustedTypedSyntax<'db>
where
    F: FnOnce(SolverEnvironment<'db, 'g>, RcValue<'db>) -> TrustedSyntax<'db>,
{
    let syn_lhs_ty = env.quote_ty(&lhs_ty);
    let Trusted(syn_rhs) = f(env.clone(), lhs_ty.clone());
    Trusted(Typed(Syntax::check_rc(syn_rhs, syn_lhs_ty), lhs_ty))
}
