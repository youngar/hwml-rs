use crate::*;

use anyhow::Result;
use hwml_core::common::*;
use hwml_core::declaration as decl;
use hwml_core::syn as core;
use hwml_core::syn::Metavariable;
use hwml_surface::syntax as surface;

pub fn infer_app<'db>(
    state: &mut State<'db>,
    app: surface::App,
) -> Result<(core::RcSyntax<'db>, core::RcSyntax<'db>)> {
    assert!(app.elements.len() >= 1);
    // Get the elaborated head of the term.
    let (mut fun_etm, mut fun_ety) = infer_type(state, *app.elements[0].clone())?;

    for arg in &app.elements[1..] {
        let domain = state.fresh_metavariable();
        state.extend_context_nameless(domain.clone());
        let codomain = state.fresh_metavariable();
        state.pop_context();
        let pi = core::Syntax::pi_rc(domain.clone(), codomain.clone());

        state.equality_constraint(
            fun_ety.clone(),
            pi.clone(),
            core::Syntax::universe_rc(UniverseLevel::new(0)),
        );

        // Check the type of the operand has the type of the domain.
        let arg_etm = check_type(state, *arg.clone(), domain.clone())?;

        // Create the core application
        let app_etm = core::Syntax::application_rc(fun_etm, arg_etm.clone());

        // Handoff for the next loop.
        fun_etm = app_etm;
        fun_ety = subst(codomain, Index::new(0), arg_etm);
    }
    // Wrap the operator in an annotation node.
    let eapp = core::Syntax::check_rc(fun_etm, fun_ety.clone());

    Ok((eapp, fun_ety))
}

pub fn infer_fun<'db>(
    state: &mut State<'db>,
    fun: surface::Fun,
) -> Result<(core::RcSyntax<'db>, core::RcSyntax<'db>)> {
    let depth = state.depth();
    // let mut types = Vec::new();
    // for group in fun.bindings.groups {
    //     let ety = elab_type(state, *group.ty)?;
    //     for binder in group.binders {
    //         // TODO: we only support simple expressions here.
    //         let surface::Expression::Id(id) = *binder else {
    //             return Err(anyhow::anyhow!("unsupported binder"));
    //         };
    //         state.extend_context(id.value, ety.clone());
    //         types.push(ety.clone());
    //     }
    // }

    // Infer the type of the body under the extended context.
    let (body, codomain) = infer_type(state, *fun.expr)?;

    // Reset the context.
    state.truncate_context(depth);

    // Build the lambda.
    let etm = core::Syntax::lambda_rc(body);

    // Build the type of the lambda.
    let mut ety = codomain;
    // for ty in types.iter().rev() {
    //     ety = core::Syntax::pi_rc(ty.clone(), ety);
    // }
    Ok((etm, ety))
}

pub fn infer_paren<'db>(
    state: &mut State<'db>,
    paren: surface::Paren,
) -> Result<(core::RcSyntax<'db>, core::RcSyntax<'db>)> {
    infer_type(state, *paren.expr)
}

pub fn infer_id<'db>(
    state: &mut State<'db>,
    id: surface::Id,
) -> Result<(core::RcSyntax<'db>, core::RcSyntax<'db>)> {
    println!("inferring id: {}", std::str::from_utf8(&id.value).unwrap());
    if *id.value == *b"Type" {
        return Ok((
            core::Syntax::universe_rc(UniverseLevel::new(0)),
            core::Syntax::universe_rc(UniverseLevel::new(1)),
        ));
    }
    if let Some(level) = state.lookup_local(&id.value) {
        let index = state.level_to_index(level);
        let ety = state.type_of(level);
        println!("found local: {:?} : {:?}", index, ety);
        return Ok((core::Syntax::variable_rc(index), ety));
    }
    todo!("global inference");
}

pub fn infer_type<'db>(
    state: &mut State<'db>,
    term: surface::Expression,
) -> Result<(core::RcSyntax<'db>, core::RcSyntax<'db>)> {
    println!("inferring type: {:?}", term);
    match term {
        surface::Expression::Fun(fun) => infer_fun(state, fun),
        surface::Expression::Paren(paren) => infer_paren(state, paren),
        surface::Expression::Id(id) => infer_id(state, id),
        _ => todo!(),
    }
}

pub fn check_pi<'db>(
    state: &mut State<'db>,
    pi: surface::Pi,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    todo!()
}

pub fn check_arrow<'db>(
    state: &mut State<'db>,
    arrow: surface::Arrow,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    todo!()
}

pub fn check_fat_arrow<'db>(
    state: &mut State<'db>,
    fat_arrow: surface::FatArrow,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    todo!()
}

pub fn check_app<'db>(
    state: &mut State<'db>,
    app: surface::App,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    let (etm, ety) = infer_app(state, app)?;
    state.equality_constraint(ty, ety, core::Syntax::universe_rc(UniverseLevel::new(0)));
    Ok(etm)
}

pub fn check_fun<'db>(
    state: &mut State<'db>,
    fun: surface::Fun,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    let (etm, ety) = infer_fun(state, fun)?;
    state.equality_constraint(ty, ety, core::Syntax::universe_rc(UniverseLevel::new(0)));
    Ok(etm)
}

pub fn check_let_in<'db>(
    state: &mut State<'db>,
    let_in: surface::LetIn,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    todo!()
}

pub fn check_underscore<'db>(
    state: &mut State<'db>,
    underscore: surface::Underscore,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    todo!()
}

pub fn check_paren<'db>(
    state: &mut State<'db>,
    paren: surface::Paren,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    check_type(state, *paren.expr, ty)
}

pub fn check_num<'db>(
    state: &mut State<'db>,
    num: surface::Num,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    todo!()
}

pub fn check_str<'db>(
    state: &mut State<'db>,
    str: surface::Str,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    todo!()
}

pub fn check_id<'db>(
    state: &mut State<'db>,
    id: surface::Id,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    let (etm, ety) = infer_id(state, id)?;
    state.equality_constraint(ety, ty, core::Syntax::universe_rc(UniverseLevel::new(0)));
    Ok(etm)
}

pub fn check_type<'db>(
    state: &mut State<'db>,
    term: surface::Expression,
    ty: core::RcSyntax<'db>,
) -> Result<core::RcSyntax<'db>> {
    match term {
        surface::Expression::Pi(pi) => check_pi(state, pi, ty),
        surface::Expression::Arrow(arrow) => check_arrow(state, arrow, ty),
        surface::Expression::FatArrow(fat_arrow) => check_fat_arrow(state, fat_arrow, ty),
        surface::Expression::App(app) => check_app(state, app, ty),
        surface::Expression::Fun(fun) => check_fun(state, fun, ty),
        surface::Expression::LetIn(let_in) => check_let_in(state, let_in, ty),
        surface::Expression::Underscore(underscore) => check_underscore(state, underscore, ty),
        surface::Expression::Paren(paren) => check_paren(state, paren, ty),
        surface::Expression::Num(num) => check_num(state, num, ty),
        surface::Expression::Str(str) => check_str(state, str, ty),
        surface::Expression::Id(id) => check_id(state, id, ty),
        _ => todo!(),
    }
}

pub fn elab_type<'db>(
    state: &mut State<'db>,
    ty: surface::Expression,
) -> Result<core::RcSyntax<'db>> {
    check_type(state, ty, core::Syntax::universe_rc(UniverseLevel::new(0)))
}

pub fn elab_def<'db>(
    db: &'db dyn salsa::Database,
    state: &mut State<'db>,
    def: surface::Def,
) -> Result<decl::Declaration<'db>> {
    let depth = state.depth();
    // A list of the elaborated types of all binders in scope.  This is used to
    // build the overall pi type of this definition.
    // let mut types = Vec::new();
    for group in def.bindings.groups {
        // Elaborate the type of the binder.
        // let ety = elab_type(state, *group.ty)?;
        // All binders in the group share the same type.
        // for binder in group.binders {
        //     // TODO: we only support simple expressions here.
        //     let surface::Expression::Id(id) = *binder else {
        //         return Err(anyhow::anyhow!("unsupported binder"));
        //     };
        //     state.extend_context(id.value, ety.clone());
        //     types.push(ety.clone());
        // }
    }
    // Elaborate the target type of the definition.
    let mut ety = match def.ty {
        Some(ty) => elab_type(state, *ty)?,
        None => {
            // If no type annotation is provided, we need to infer it
            // For now, we'll use a placeholder or error
            return Err(anyhow::anyhow!("type inference not yet implemented"));
        }
    };
    // Check the body of the definition.
    let mut etm = check_type(state, *def.value, ety.clone())?;

    // Reset the context.
    state.truncate_context(depth);

    // Build the Pi type and Lamba.
    // for ty in types.iter().rev() {
    //     ety = core::Syntax::pi_rc(ety.clone(), ty.clone());
    //     etm = core::Syntax::lambda_rc(etm);
    // }

    // TODO: !!! EXTEND CONTEXT WITH THE GLOBAL DEFINTION

    // Convert the surface ID to a string and then to a ConstantId
    let name_str = std::str::from_utf8(&def.id.value).unwrap();
    let name_id = core::ConstantId::from_str(db, name_str);

    Ok(decl::Declaration::constant(name_id, ety, etm))
}

pub fn go<'db>(
    db: &'db dyn salsa::Database,
    program: surface::Program,
) -> Result<Vec<decl::Declaration<'db>>> {
    let mut state = State::new();

    let mut declarations = Vec::new();
    for stmt in program.statements {
        match stmt {
            surface::Statement::Def(def) => declarations.push(elab_def(db, &mut state, def)?),
            _ => {}
        }
    }

    for constraint in state.constraints {
        println!("constraint: {:?}", constraint);
    }
    Ok(declarations)
}
