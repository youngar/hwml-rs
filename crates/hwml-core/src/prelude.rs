//! Inject basic definitions into the global environment.

use crate::*;
use hwml_support::IntoWithDb;
use syn::Syntax;
use val::{DataConstructorInfo, GlobalEnv, TypeConstructorInfo};

pub fn def_bool<'db>(db: &'db Database, g: &mut GlobalEnv<'db>) {
    let bool_id = "Bool".into_with_db(db);
    let bool_tm = Syntax::type_constructor_rc(bool_id, vec![]);
    g.add_type_constructor(
        bool_id,
        TypeConstructorInfo::new([], 0, UniverseLevel::new(0)),
    );
    g.add_data_constructor(
        "True".into_with_db(db),
        DataConstructorInfo::new([], bool_tm.clone()),
    );
    g.add_data_constructor(
        "False".into_with_db(db),
        DataConstructorInfo::new([], bool_tm.clone()),
    );
}

pub fn def_nat<'db>(db: &'db Database, g: &mut GlobalEnv<'db>) {
    let nat_id = "Nat".into_with_db(db);
    let nat_tm = Syntax::type_constructor_rc(nat_id, vec![]);
    g.add_type_constructor(
        nat_id,
        TypeConstructorInfo::new([], 0, UniverseLevel::new(0)),
    );
    g.add_data_constructor(
        "Zero".into_with_db(db),
        DataConstructorInfo::new([], nat_tm.clone()),
    );
    g.add_data_constructor(
        "Succ".into_with_db(db),
        DataConstructorInfo::new([nat_tm.clone()], nat_tm),
    );
}

pub fn load<'db>(db: &'db Database, g: &mut GlobalEnv<'db>) {
    def_bool(db, g);
    def_nat(db, g);
}
