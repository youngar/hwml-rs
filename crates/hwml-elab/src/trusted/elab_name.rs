use crate::*;
use hwml_core::*;

pub fn elab_name<'db, 'g>(
    env: SolverEnvironment<'db, 'g>,
    loc: Option<SourceRange<'db>>,
    name: Name<'db>,
) -> TrustedTypedSyntax<'db> {
    match env.resolve(name) {
        Some(typed_term) => Trusted(typed_term),
        None => {
            print!("unknown name!!! {:}", name.to_string(env.db()));
            let ty = env.fresh_meta(Value::universe_rc(UniverseLevel::new(0)), loc.clone());
            Trusted(Typed(env.quote(&env.fresh_meta(ty.clone(), loc), &ty), ty))
        }
    }
}
