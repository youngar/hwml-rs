use lalrpop_util::lalrpop_mod;

pub mod cst;

lalrpop_mod!(
    #[allow(clippy::ptr_arg)]
    #[rustfmt::skip]
    pub grammar
);
