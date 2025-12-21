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

pub fn def_vec<'db>(db: &'db Database, g: &mut GlobalEnv<'db>) {
    let nat_id = "Nat".into_with_db(db);
    let vec_id = "Vec".into_with_db(db);
    // |- vec (a : type) : nat -> type.
    g.add_type_constructor(
        vec_id,
        TypeConstructorInfo {
            arguments: [
                Syntax::universe_rc(UniverseLevel::new(0)),
                Syntax::type_constructor_rc(nat_id, vec![]),
            ]
            .into(),
            num_parameters: 1,
            level: UniverseLevel::new(0),
        },
    );
    // a : type |- vnil : vec a 0
    g.add_data_constructor(
        "VNil".into_with_db(db),
        DataConstructorInfo {
            arguments: [].into(),
            // vec a 0
            ty: Syntax::type_constructor_rc(
                vec_id,
                [
                    Syntax::variable_rc(Index(0)),
                    Syntax::data_constructor_rc("Zero".into_with_db(db), [].into()),
                ]
                .into(),
            ),
        },
    );
    // a : type |- vcons (n : nat) (x : a) (xs : vec a n) : vec a (suc n)
    g.add_data_constructor(
        "VCons".into_with_db(db),
        DataConstructorInfo {
            arguments: [
                Syntax::type_constructor_rc(nat_id, vec![]), // n : nat
                Syntax::variable_rc(Index(1)),               // x : a
                // xs : vec a n
                Syntax::type_constructor_rc(
                    vec_id,
                    [
                        Syntax::variable_rc(Index(2)), // a
                        Syntax::variable_rc(Index(1)), // n
                    ]
                    .into(),
                ),
            ]
            .into(),
            // vec a (succ n)
            ty: Syntax::type_constructor_rc(
                vec_id,
                [
                    Syntax::variable_rc(Index(3)), // a
                    Syntax::data_constructor_rc(
                        "Succ".into_with_db(db),
                        [Syntax::variable_rc(Index(2))].into(), // n
                    ),
                ]
                .into(),
            ),
        },
    );
}

pub fn load<'db>(db: &'db Database, g: &mut GlobalEnv<'db>) {
    def_bool(db, g);
    def_nat(db, g);
    def_option(db, g);
    def_vec(db, g);
}
