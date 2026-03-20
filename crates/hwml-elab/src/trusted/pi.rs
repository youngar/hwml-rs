use crate::*;
use hwml_core::*;

pub fn pi<'db, 'g, T>(
    mut env: SolverEnvironment<'db, 'g>,
    source: TypeTactic<'db>,
    target: T,
) -> TrustedValue<'db>
where
    T: FnOnce(SolverEnvironment<'db, 'g>) -> TrustedValue<'db>,
{
    let universe = Value::universe_rc(UniverseLevel::new(0));
    let Trusted(source) = source;
    let Binding(Trusted(target)) =
        env.under_binder(None, source.clone(), |env| target(env.clone()));
    let target_closure = env.make_closure(Binding(&target), &universe);
    Trusted(Value::pi_rc(source, target_closure))
}
