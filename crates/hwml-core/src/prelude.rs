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
        TypeConstructorInfo {
            arguments: [].into(),
            num_parameters: 0,
            level: UniverseLevel::new(0),
        },
    );
    g.add_data_constructor(
        "True".into_with_db(db),
        DataConstructorInfo {
            arguments: [].into(),
            ty: bool_tm.clone(),
        },
    );
    g.add_data_constructor(
        "False".into_with_db(db),
        DataConstructorInfo {
            arguments: [].into(),
            ty: bool_tm.clone(),
        },
    );
}

pub fn def_nat<'db>(db: &'db Database, g: &mut GlobalEnv<'db>) {
    let nat_id = "Nat".into_with_db(db);
    let nat_tm = Syntax::type_constructor_rc(nat_id, vec![]);
    g.add_type_constructor(
        nat_id,
        TypeConstructorInfo {
            arguments: [].into(),
            num_parameters: 0,
            level: UniverseLevel::new(0),
        },
    );
    g.add_data_constructor(
        "Zero".into_with_db(db),
        DataConstructorInfo {
            arguments: [].into(),
            ty: nat_tm.clone(),
        },
    );
    g.add_data_constructor(
        "Succ".into_with_db(db),
        DataConstructorInfo {
            arguments: [nat_tm.clone()].into(),
            ty: nat_tm,
        },
    );
}

pub fn def_option<'db>(db: &'db Database, g: &mut GlobalEnv<'db>) {
    let option_id = "Option".into_with_db(db);
    g.add_type_constructor(
        option_id,
        TypeConstructorInfo {
            arguments: [Syntax::universe_rc(UniverseLevel::new(0))].into(),
            num_parameters: 1,
            level: UniverseLevel::new(0),
        },
    );
    g.add_data_constructor(
        "None".into_with_db(db),
        DataConstructorInfo {
            arguments: [].into(),
            ty: Syntax::type_constructor_rc(option_id, vec![Syntax::variable_rc(Index(0))]),
        },
    );
    g.add_data_constructor(
        "Some".into_with_db(db),
        DataConstructorInfo {
            arguments: [Syntax::variable_rc(Index(0))].into(),
            ty: Syntax::type_constructor_rc(option_id, vec![Syntax::variable_rc(Index(1))]),
        },
    )
}

pub fn load<'db>(db: &'db Database, g: &mut GlobalEnv<'db>) {
    def_bool(db, g);
    def_nat(db, g);
    def_option(db, g);
}
