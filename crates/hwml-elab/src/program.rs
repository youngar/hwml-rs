use std::rc::Rc;

use hwml_core::{
    UniverseLevel,
    val::{ConstantInfo, GlobalEnv, PrimitiveInfo, TypeConstructorInfo},
    QualifiedName,
};
use hwml_surface::{Program, Statement};

use crate::{
    ctx::ElabCtx,
    elab::{self, Elaborator},
    error::ElabError,
    names::{GlobalNameKind, GlobalNameTable, RcGlobalNameTable, bytes_to_simple_qname},
    state::SolverState,
    zonk::{substitute_metas_in_syntax, zonk},
};

/// An elaborated top-level declaration.
#[derive(Debug, Clone)]
pub enum ElaboratedDecl<'db> {
    Constant { name: QualifiedName<'db>, info: ConstantInfo<'db> },
    Primitive { name: QualifiedName<'db>, info: PrimitiveInfo<'db> },
    TypeConstructor { name: QualifiedName<'db>, info: TypeConstructorInfo<'db> },
}

/// Result of elaborating a surface `Program`.
pub struct ElabProgramResult<'db> {
    pub decls: Vec<ElaboratedDecl<'db>>,
    pub errors: Vec<ElabError<'db>>,
}

/// Elaborate all declarations in a surface `Program`, accumulating errors.
///
/// Declarations are processed in order. Each successful declaration is added
/// to `global` so later declarations can reference earlier ones.
pub fn elab_program<'db>(
    db: &'db dyn salsa::Database,
    global: &mut GlobalEnv<'db>,
    program: &Program,
) -> ElabProgramResult<'db> {
    let mut decls = Vec::new();
    let mut errors = Vec::new();
    let mut name_table: GlobalNameTable<'db> = GlobalNameTable::new();

    elab_statements(db, global, &program.statements, None, &mut name_table, &mut decls, &mut errors);

    ElabProgramResult { decls, errors }
}

fn elab_statements<'db>(
    db: &'db dyn salsa::Database,
    global: &mut GlobalEnv<'db>,
    statements: &[Statement],
    namespace: Option<QualifiedName<'db>>,
    name_table: &mut GlobalNameTable<'db>,
    decls: &mut Vec<ElaboratedDecl<'db>>,
    errors: &mut Vec<ElabError<'db>>,
) {
    for stmt in statements {
        match stmt {
            Statement::Def(def) => {
                let qname = bytes_to_simple_qname(db, namespace, &def.id.value);
                let rc_names: RcGlobalNameTable<'db> = Rc::new(name_table.clone());
                // Elaborate inside a block so `global` borrow ends before mutation.
                let result: Result<ConstantInfo<'db>, ElabError<'db>> = {
                    let mut state = SolverState::new();
                    let mut elab = Elaborator::new_with_names(
                        global,
                        ElabCtx::empty(),
                        &mut state,
                        rc_names,
                    );
                    elab::decl::elab_constant(&mut elab, def).and_then(|elaborated| {
                        zonk(&mut state)?;
                        let ty = substitute_metas_in_syntax(&elaborated.ty, &state);
                        let val = substitute_metas_in_syntax(&elaborated.value, &state);
                        Ok(ConstantInfo::new(ty, val))
                    })
                };
                match result {
                    Ok(info) => {
                        global.add_constant(qname, info.clone());
                        name_table.insert(def.id.value.to_vec(), (qname, GlobalNameKind::Constant));
                        decls.push(ElaboratedDecl::Constant { name: qname, info });
                    }
                    Err(e) => errors.push(e),
                }
            }
            Statement::Prim(prim) => {
                let qname = bytes_to_simple_qname(db, namespace, &prim.id.value);
                let rc_names: RcGlobalNameTable<'db> = Rc::new(name_table.clone());
                let result: Result<PrimitiveInfo<'db>, ElabError<'db>> = {
                    let mut state = SolverState::new();
                    let mut elab = Elaborator::new_with_names(
                        global,
                        ElabCtx::empty(),
                        &mut state,
                        rc_names,
                    );
                    use hwml_core::ty::Ty;
                    elab::expr::check(&mut elab, &prim.ty, Rc::new(Ty::UniverseType))
                        .and_then(|checked| {
                            zonk(&mut state)?;
                            let ty = substitute_metas_in_syntax(&checked.into_inner(), &state);
                            Ok(PrimitiveInfo::new(ty))
                        })
                };
                match result {
                    Ok(info) => {
                        global.add_primitive(qname, info.clone());
                        name_table.insert(prim.id.value.to_vec(), (qname, GlobalNameKind::Primitive));
                        decls.push(ElaboratedDecl::Primitive { name: qname, info });
                    }
                    Err(e) => errors.push(e),
                }
            }
            Statement::Inductive(ind) => {
                let qname = bytes_to_simple_qname(db, namespace, &ind.name.value);
                let rc_names: RcGlobalNameTable<'db> = Rc::new(name_table.clone());
                let result: Result<TypeConstructorInfo<'db>, ElabError<'db>> = {
                    let mut state = SolverState::new();
                    let mut elab = Elaborator::new_with_names(
                        global,
                        ElabCtx::empty(),
                        &mut state,
                        rc_names,
                    );
                    elab::decl::elab_inductive(&mut elab, ind).and_then(|elaborated| {
                        zonk(&mut state)?;
                        let num_params = elaborated.params.len();
                        let args: Vec<_> = elaborated
                            .params
                            .iter()
                            .chain(elaborated.indices.iter())
                            .map(|s| substitute_metas_in_syntax(s, &state))
                            .collect();
                        let universe_syn = substitute_metas_in_syntax(&elaborated.universe, &state);
                        let level = extract_universe_level(&universe_syn);
                        Ok(TypeConstructorInfo::new(args, num_params, UniverseLevel::new(level)))
                    })
                };
                match result {
                    Ok(info) => {
                        global.add_type_constructor(qname, info.clone());
                        name_table.insert(ind.name.value.to_vec(), (qname, GlobalNameKind::TypeConstructor));
                        decls.push(ElaboratedDecl::TypeConstructor { name: qname, info });
                    }
                    Err(e) => errors.push(e),
                }
            }
            Statement::Namespace(ns) => {
                let ns_qname = bytes_to_simple_qname(db, namespace, &ns.name.value);
                elab_statements(db, global, &ns.statements, Some(ns_qname), name_table, decls, errors);
            }
            Statement::Open(_) | Statement::Meta(_) => {}
        }
    }
}

/// Extract universe level from a `Syntax::UniverseCode(n)` node. Defaults to 0.
fn extract_universe_level(syn: &hwml_core::Syntax) -> usize {
    match syn {
        hwml_core::Syntax::UniverseCode(n) => *n,
        _ => 0,
    }
}
