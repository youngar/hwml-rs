use hwml_core::{Name, QualifiedName};
use hwml_surface::{Expression, Statement};
/// Strongly Connected Components (SCC) computation for declaration-level mutual recursion.
///
/// This module implements Tarjan's algorithm to group mutually recursive declarations
/// into SCCs, enabling order-independent elaboration with forward references.
use std::collections::{HashMap, HashSet};

use crate::kernel::extract_binder_name;
use crate::util::surface_id_to_path;

/// A strongly connected component of declarations.
/// Contains indices into the original statement list.
#[derive(Debug, Clone)]
pub struct Scc {
    /// Indices of statements in this SCC (in original source order)
    pub indices: Vec<usize>,
}

/// Extract all QualifiedName references from a surface expression.
/// Tracks local binders to avoid false dependencies on shadowed names.
fn extract_expr_refs<'db>(
    db: &'db dyn salsa::Database,
    expr: &Expression,
    refs: &mut HashSet<Vec<Name<'db>>>,
    locals: &mut HashSet<Vec<u8>>, // Track locally bound names (as raw bytes)
) {
    match expr {
        Expression::Id(id) => {
            // Only add as dependency if NOT locally bound
            if !locals.contains(&id.value.as_bytes().to_vec()) {
                if let Ok(path) = surface_id_to_path(db, id) {
                    if !path.is_empty() {
                        refs.insert(path);
                    }
                }
            }
        }
        Expression::App(app) => {
            for elem in &app.elements {
                extract_expr_refs(db, elem, refs, locals);
            }
        }
        Expression::Pi(pi) => {
            // Elaborate type annotations first (before binders are in scope)
            for group in &pi.bindings.groups {
                extract_expr_refs(db, &group.ty, refs, locals);
            }
            // Clone locals and add binders for target elaboration
            let mut extended_locals = locals.clone();
            for group in &pi.bindings.groups {
                for binder in &group.binders {
                    if let Some(name) = extract_binder_name(binder) {
                        extended_locals.insert(name.as_bytes().to_vec());
                    }
                }
            }
            extract_expr_refs(db, &pi.target, refs, &mut extended_locals);
            // Note: we don't modify the original `locals` - scope properly isolated
        }
        Expression::Arrow(arrow) => {
            extract_expr_refs(db, &arrow.source, refs, locals);
            extract_expr_refs(db, &arrow.target, refs, locals);
        }
        Expression::Fun(fun) => {
            // Elaborate type annotations first (before binders are in scope)
            for group in &fun.bindings.groups {
                if let hwml_surface::BindingGroup::Typed(tg) = group {
                    extract_expr_refs(db, &tg.ty, refs, locals);
                }
            }
            // Clone locals and add binders for body elaboration
            let mut extended_locals = locals.clone();
            for group in &fun.bindings.groups {
                match group {
                    hwml_surface::BindingGroup::Typed(tg) => {
                        for binder in &tg.binders {
                            if let hwml_surface::Pattern::Id(id) = &binder.pattern {
                                extended_locals.insert(id.value.as_bytes().to_vec());
                            }
                        }
                    }
                    hwml_surface::BindingGroup::Untyped(ug) => {
                        for binder in &ug.binders {
                            if let hwml_surface::Pattern::Id(id) = &binder.pattern {
                                extended_locals.insert(id.value.as_bytes().to_vec());
                            }
                        }
                    }
                }
            }
            extract_expr_refs(db, &fun.expr, refs, &mut extended_locals);
        }
        Expression::LetIn(let_in) => {
            // Elaborate type and value first (before let-binder is in scope)
            if let Some(ty) = &let_in.ty {
                extract_expr_refs(db, ty, refs, locals);
            }
            extract_expr_refs(db, &let_in.value, refs, locals);
            // Clone locals and add let-bound name for body elaboration
            let mut extended_locals = locals.clone();
            extended_locals.insert(let_in.id.value.as_bytes().to_vec());
            extract_expr_refs(db, &let_in.expr, refs, &mut extended_locals);
        }
        Expression::Match(m) => {
            extract_expr_refs(db, &m.scrutinee, refs, locals);
            for clause in &m.clauses {
                // TODO: Handle pattern binders properly when match is fully implemented
                extract_expr_refs(db, &clause.body, refs, locals);
            }
        }
        Expression::Paren(p) => {
            extract_expr_refs(db, &p.expr, refs, locals);
        }
        Expression::Dot(dot) => {
            // Elaborate receiver, field name doesn't contribute dependencies
            extract_expr_refs(db, &dot.receiver, refs, locals);
        }
        Expression::TypeAscription(asc) => {
            extract_expr_refs(db, &asc.expr, refs, locals);
            extract_expr_refs(db, &asc.ty, refs, locals);
        }
        // Terminal cases: no recursive refs
        Expression::Universe(_)
        | Expression::Num(_)
        | Expression::Str(_)
        | Expression::Underscore(_)
        | Expression::FatArrow(_)
        | Expression::Error(_)
        | Expression::Hole(_) => {}
    }
}

/// Extract dependencies from a statement.
/// Returns a list of paths (not yet qualified) that this statement references.
/// Properly handles lexical scoping to avoid false dependencies on shadowed names.
pub fn extract_statement_deps<'db>(
    db: &'db dyn salsa::Database,
    stmt: &Statement,
) -> HashSet<Vec<Name<'db>>> {
    let mut refs = HashSet::new();
    let mut locals = HashSet::new(); // Track locally bound names

    match stmt {
        Statement::Def(def) => {
            // Type annotation (before binders are in scope)
            if let Some(ty) = &def.ty {
                extract_expr_refs(db, ty, &mut refs, &mut locals);
            }
            // Bindings - add type annotations, then add binders to locals
            for group in &def.bindings.groups {
                if let hwml_surface::BindingGroup::Typed(tg) = group {
                    extract_expr_refs(db, &tg.ty, &mut refs, &mut locals);
                    // Add binders to locals for value elaboration
                    for binder in &tg.binders {
                        if let hwml_surface::Pattern::Id(id) = &binder.pattern {
                            locals.insert(id.value.as_bytes().to_vec());
                        }
                    }
                }
            }
            // Value (with binders in scope)
            extract_expr_refs(db, &def.value, &mut refs, &mut locals);
        }
        Statement::Inductive(ind) => {
            // Parameters - types, then add to locals
            for group in &ind.parameters.groups {
                extract_expr_refs(db, &group.ty, &mut refs, &mut locals);
                for binder in &group.binders {
                    if let Some(name) = extract_binder_name(binder) {
                        locals.insert(name.as_bytes().to_vec());
                    }
                }
            }
            // Indices - types, then add to locals
            for group in &ind.indices.groups {
                extract_expr_refs(db, &group.ty, &mut refs, &mut locals);
                for binder in &group.binders {
                    if let Some(name) = extract_binder_name(binder) {
                        locals.insert(name.as_bytes().to_vec());
                    }
                }
            }
            // Universe (with params and indices in scope)
            extract_expr_refs(db, &ind.universe, &mut refs, &mut locals);
            // Constructors (with params in scope, NOT indices - those are in return type)
            // Clear indices from locals
            for group in &ind.indices.groups {
                for binder in &group.binders {
                    if let Some(name) = extract_binder_name(binder) {
                        locals.remove(&name.as_bytes().to_vec());
                    }
                }
            }
            for ctor in &ind.constructors {
                extract_expr_refs(db, &ctor.ty, &mut refs, &mut locals);
            }
        }
        Statement::Prim(prim) => {
            extract_expr_refs(db, &prim.ty, &mut refs, &mut locals);
        }
        // Meta, Open, Namespace, Invalid don't contribute to dependency graph
        Statement::Meta(_) | Statement::Open(_) | Statement::Namespace(_) | Statement::Invalid(_) => {}
    }

    refs
}

/// Get the declared name of a statement (if any).
pub fn statement_declares<'db>(
    db: &'db dyn salsa::Database,
    stmt: &Statement,
) -> Option<Vec<Name<'db>>> {
    match stmt {
        Statement::Def(def) => surface_id_to_path(db, &def.id)
            .ok()
            .filter(|p| !p.is_empty()),
        Statement::Inductive(ind) => surface_id_to_path(db, &ind.name)
            .ok()
            .filter(|p| !p.is_empty()),
        Statement::Prim(prim) => surface_id_to_path(db, &prim.id)
            .ok()
            .filter(|p| !p.is_empty()),
        Statement::Meta(meta) => surface_id_to_path(db, &meta.id)
            .ok()
            .filter(|p| !p.is_empty()),
        Statement::Open(_) | Statement::Namespace(_) | Statement::Invalid(_) => None,
    }
}

/// Information about a declaration needed for SCC computation.
///
/// CRITICAL: Each declaration stores the `Resolver` that was active in its file.
/// While namespaces span files, `open` statements are file-local. This ensures
/// that declarations from different files with different `open` statements
/// don't accidentally share resolver state during elaboration.
///
/// Additionally, each declaration tracks its source file for accurate error reporting.
#[derive(Debug, Clone)]
pub struct DeclInfo<'db> {
    pub index: usize,
    pub qualified_name: QualifiedName<'db>,
    pub stmt: Statement,
    /// The resolver state that was active when this declaration was declared.
    /// Captures file-local `open` statements.
    pub resolver: crate::resolver::Resolver<'db>,
    /// The source file where this declaration was written.
    /// Used for error reporting to show real file names instead of "synthetic".
    pub source: hwml_core::Source<'db>,
}

/// Validate that all mutually recursive definitions have type annotations.
///
/// Rule: Unannotated `def`s are only allowed in SCCs of size 1.
/// If an SCC has size > 1 and contains an unannotated `def`, this returns an error.
pub fn validate_scc_annotations<'db>(scc: &Scc, decls: &[DeclInfo<'db>]) -> Result<(), String> {
    // Single-element SCCs can be unannotated
    if scc.indices.len() == 1 {
        return Ok(());
    }

    // Check all defs in this SCC for type annotations
    for &idx in &scc.indices {
        if let Statement::Def(def) = &decls[idx].stmt {
            if def.ty.is_none() {
                return Err(format!(
                    "Mutually recursive definition '{}' requires an explicit type annotation",
                    &def.id.value
                ));
            }
        }
    }

    Ok(())
}

/// Compute strongly connected components at the LIBRARY level.
/// This is critical: namespaces can span multiple files, so SCC computation
/// must happen across the entire library, not per-file or per-block.
///
/// Returns SCCs in reverse topological order (dependencies first).
pub fn compute_library_sccs<'db>(
    db: &'db dyn salsa::Database,
    decls: &[DeclInfo<'db>],
    stub_table: &crate::stub_table::StubTable<'db>,
) -> Vec<Scc> {
    // Build qualified name → index map
    let mut name_to_idx: HashMap<QualifiedName<'db>, usize> = HashMap::new();
    for decl in decls {
        name_to_idx.insert(decl.qualified_name, decl.index);
    }

    // Build adjacency list (index → indices of dependencies)
    let mut graph: Vec<Vec<usize>> = vec![Vec::new(); decls.len()];
    for decl in decls {
        let dep_paths = extract_statement_deps(db, &decl.stmt);

        // Resolve each dependency path to a qualified name using stub table
        for dep_path in dep_paths {
            // Try to qualify against the declaring namespace
            let declaring_namespace = decl.qualified_name.namespace(db);

            // Resolve using namespace walking (like the resolver does)
            if let Some(qualified) =
                resolve_dep_in_library(db, &dep_path, declaring_namespace, stub_table)
            {
                // Check if this dependency is declared in this library
                if let Some(&dep_idx) = name_to_idx.get(&qualified) {
                    if dep_idx != decl.index {
                        graph[decl.index].push(dep_idx);
                    }
                }
            }
        }
    }

    // Run Tarjan's algorithm
    tarjan_scc(&graph)
}

/// Resolve a dependency path within the library.
/// This uses the same scoping rules as the resolver but simplified for SCC computation.
fn resolve_dep_in_library<'db>(
    db: &'db dyn salsa::Database,
    path: &[Name<'db>],
    from_namespace: Option<QualifiedName<'db>>,
    stub_table: &crate::stub_table::StubTable<'db>,
) -> Option<QualifiedName<'db>> {
    // Try qualifying against the current namespace and walk up
    let mut current_ns = from_namespace;
    loop {
        if let Some(qualified) = QualifiedName::qualify_path(db, current_ns, path) {
            if stub_table.contains(qualified) {
                return Some(qualified);
            }
        }

        // Walk up to parent namespace
        match current_ns {
            Some(ns) => current_ns = ns.namespace(db),
            None => break,
        }
    }

    None
}

/// Tarjan's strongly connected components algorithm.
/// Returns SCCs in reverse topological order.
fn tarjan_scc(graph: &[Vec<usize>]) -> Vec<Scc> {
    let n = graph.len();
    let mut index = 0;
    let mut stack = Vec::new();
    let mut on_stack = vec![false; n];
    let mut indices = vec![None; n];
    let mut lowlinks = vec![0; n];
    let mut sccs = Vec::new();

    fn strongconnect(
        v: usize,
        graph: &[Vec<usize>],
        index: &mut usize,
        stack: &mut Vec<usize>,
        on_stack: &mut [bool],
        indices: &mut [Option<usize>],
        lowlinks: &mut [usize],
        sccs: &mut Vec<Scc>,
    ) {
        indices[v] = Some(*index);
        lowlinks[v] = *index;
        *index += 1;
        stack.push(v);
        on_stack[v] = true;

        for &w in &graph[v] {
            if indices[w].is_none() {
                strongconnect(w, graph, index, stack, on_stack, indices, lowlinks, sccs);
                lowlinks[v] = lowlinks[v].min(lowlinks[w]);
            } else if on_stack[w] {
                lowlinks[v] = lowlinks[v].min(indices[w].unwrap());
            }
        }

        if lowlinks[v] == indices[v].unwrap() {
            let mut scc_indices = Vec::new();
            loop {
                let w = stack.pop().unwrap();
                on_stack[w] = false;
                scc_indices.push(w);
                if w == v {
                    break;
                }
            }
            // Sort by original source order for deterministic output
            scc_indices.sort_unstable();
            sccs.push(Scc {
                indices: scc_indices,
            });
        }
    }

    for v in 0..n {
        if indices[v].is_none() {
            strongconnect(
                v,
                graph,
                &mut index,
                &mut stack,
                &mut on_stack,
                &mut indices,
                &mut lowlinks,
                &mut sccs,
            );
        }
    }

    // Tarjan returns SCCs in reverse topological order, which is what we want
    sccs
}
