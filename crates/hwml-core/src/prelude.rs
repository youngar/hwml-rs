//! Inject basic definitions into the global environment.

use crate::*;
use hwml_support::IntoWithDb;
use syn::Syntax;
use val::{DataConstructorInfo, GlobalEnv, TypeConstructorInfo};

pub fn def_bool<'db, 'a, Db: salsa::Database>(db: &'db Db, g: &'a mut GlobalEnv<'db>) {
    let bool_id = "Bool".into_with_db(db);
    let bool = Syntax::type_constructor_rc(bool_id, vec![]);
    g.add_type_constructor(
        bool_id,
        TypeConstructorInfo::new(vec![].into(), 0, UniverseLevel::new(0)),
    );
    g.add_data_constructor(
        "True".into_with_db(db),
        DataConstructorInfo::new(vec![].into(), bool.clone()),
    );
    g.add_data_constructor(
        "False".into_with_db(db),
        DataConstructorInfo::new(vec![].into(), bool.clone()),
    );
}

pub fn def_nat<'db, 'a, Db: salsa::Database>(db: &'db Db, g: &'a mut GlobalEnv<'db>) {
    let nat_id = "Nat".into_with_db(db);
    let nat = Syntax::type_constructor_rc(nat_id, vec![]);
    g.add_type_constructor(
        nat_id,
        TypeConstructorInfo::new(vec![].into(), 0, UniverseLevel::new(0)),
    );
    g.add_data_constructor(
        "Z".into_with_db(db),
        DataConstructorInfo::new(
            vec![].into(), // no arguments
            nat.clone(),
        ),
    );
    g.add_data_constructor(
        "S".into_with_db(db),
        DataConstructorInfo::new(vec![nat.clone()].into(), nat.clone()),
    );
}
