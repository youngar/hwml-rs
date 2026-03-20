use crate::*;
use hwml_core::*;

pub fn decode<'db, 'g>(
    env: SolverEnvironment<'db, 'g>,
    rhs: TrustedTypedSyntax<'db>,
) -> TrustedSemType<'db> {
    let sem_lhs_ty = Value::universe_rc(UniverseLevel::new(0));
    let sem_lhs = env.fresh_meta(sem_lhs_ty.clone(), None);

    let Trusted(Typed(syn_rhs, sem_rhs_ty)) = rhs;
    let sem_rhs = env.eval(&syn_rhs);

    let meta = sem_lhs.clone();
    let bg = env.clone();

    env.constrain(async move {
        unify_ty(bg.clone(), sem_lhs_ty.clone(), sem_rhs_ty)
            .await
            .unwrap();
        unify(bg.db(), bg, sem_lhs, sem_rhs, sem_lhs_ty)
            .await
            .unwrap();
    });

    Trusted(Type(meta))
}
