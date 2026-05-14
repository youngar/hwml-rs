//! AST Validation
//!
//! Debug-mode validation of parsed AST structure, inspired by Carbon's Tree::Verify().
//!
//! This catches parser bugs by verifying structural invariants that should always hold.
//! Only enabled in debug builds to avoid performance overhead in release builds.

use crate::syntax::*;

/// Verify that a program's AST structure is valid.
///
/// This is a debug-only validation that panics if any structural invariants are violated.
/// It catches parser bugs early by checking:
/// - Expression structures are valid (e.g., App has ≥2 elements)
/// - Identifiers are not error markers
/// - Match expressions have valid structure
/// - No orphaned or malformed nodes
///
/// # Panics
/// Panics if validation fails (debug builds only)
#[cfg(debug_assertions)]
pub fn verify_program(program: &Program) {
    for stmt in &program.statements {
        verify_statement(stmt);
    }
}

/// No-op in release builds
#[cfg(not(debug_assertions))]
pub fn verify_program(_program: &Program) {}

#[cfg(debug_assertions)]
fn verify_statement(stmt: &Statement) {
    match stmt {
        Statement::Def(def) => {
            verify_id(&def.id);
            verify_bindings(&def.bindings);
            if let Some(ty) = &def.ty {
                verify_expression(ty);
            }
            verify_expression(&def.value);
        }
        Statement::Meta(meta) => {
            verify_id(&meta.id);
            verify_bindings(&meta.bindings);
            if let Some(ty) = &meta.ty {
                verify_expression(ty);
            }
            verify_expression(&meta.value);
        }
        Statement::Prim(prim) => {
            verify_id(&prim.id);
            verify_expression(&prim.ty);
        }
        Statement::Namespace(ns) => {
            verify_id(&ns.name);
            for stmt in &ns.statements {
                verify_statement(stmt);
            }
        }
        Statement::Open(_) => {
            // Open statements are simple, nothing to deeply validate
        }
        Statement::Inductive(ind) => {
            verify_id(&ind.name);
            verify_typed_bindings(&ind.parameters);
            verify_expression(&ind.universe);
            verify_typed_bindings(&ind.indices);
            for ctor in &ind.constructors {
                verify_constructor(ctor);
            }
        }
        Statement::Invalid(_) => {
            // Error statements are expected to exist
        }
    }
}

#[cfg(debug_assertions)]
fn verify_expression(expr: &Expression) {
    match expr {
        Expression::Id(id) => {
            verify_id(id);
        }
        Expression::App(app) => {
            assert!(
                app.elements.len() >= 2,
                "App expression must have at least 2 elements, found {}",
                app.elements.len()
            );
            for elem in &app.elements {
                verify_expression(elem);
            }
        }
        Expression::Match(m) => {
            verify_expression(&m.scrutinee);
            for clause in &m.clauses {
                verify_pattern(&clause.pattern);
                verify_expression(&clause.body);
            }
        }
        Expression::Fun(fun) => {
            verify_bindings(&fun.bindings);
            verify_expression(&fun.expr);
        }
        Expression::Pi(pi) => {
            verify_typed_bindings(&pi.bindings);
            verify_expression(&pi.target);
        }
        Expression::Arrow(arrow) => {
            verify_expression(&arrow.source);
            verify_expression(&arrow.target);
        }
        Expression::TypeAscription(asc) => {
            verify_expression(&asc.expr);
            verify_expression(&asc.ty);
        }
        Expression::Paren(paren) => {
            verify_expression(&paren.expr);
        }
        Expression::FatArrow(fa) => {
            verify_expression(&fa.source);
            verify_expression(&fa.target);
        }
        Expression::LetIn(let_in) => {
            verify_bindings(&let_in.bindings);
            if let Some(ty) = &let_in.ty {
                verify_expression(ty);
            }
            verify_expression(&let_in.value);
            verify_expression(&let_in.expr);
        }
        Expression::Dot(dot) => {
            verify_expression(&dot.receiver);
            verify_id(&dot.field);
        }
        Expression::Num(_)
        | Expression::Hole(_)
        | Expression::Universe(_)
        | Expression::Underscore(_)
        | Expression::Error(_)
        | Expression::Str(_) => {
            // These are atomic, nothing to recursively verify
        }
    }
}

#[cfg(debug_assertions)]
fn verify_pattern(pattern: &Pattern) {
    match pattern {
        Pattern::Id(id) => verify_id(id),
        Pattern::AppSeq(app) => {
            assert!(
                app.items.len() >= 2,
                "Pattern AppSeq must have at least 2 elements, found {}",
                app.items.len()
            );
            for elem in &app.items {
                verify_pattern(elem);
            }
        }
        Pattern::As(as_pat) => {
            verify_pattern(&as_pat.pattern);
            verify_id(&as_pat.name);
        }
        Pattern::Paren(paren) => {
            verify_pattern(&paren.inner);
        }
        Pattern::Num(_) | Pattern::Underscore(_) | Pattern::Error(_) | Pattern::Str(_) => {
            // Atomic patterns, nothing to verify
        }
    }
}

#[cfg(debug_assertions)]
fn verify_id(id: &Id) {
    assert!(!id.value.is_empty(), "Identifier must not be empty");
    assert!(
        &*id.value != "<error>",
        "Identifier should not be the error marker '<error>'"
    );
}

#[cfg(debug_assertions)]
fn verify_bindings(bindings: &Bindings) {
    for group in &bindings.groups {
        match group {
            BindingGroup::Typed(typed) => {
                for binder in &typed.binders {
                    verify_pattern(&binder.pattern);
                }
                verify_expression(&typed.ty);
            }
            BindingGroup::Untyped(untyped) => {
                for binder in &untyped.binders {
                    verify_pattern(&binder.pattern);
                }
            }
        }
    }
}

#[cfg(debug_assertions)]
fn verify_typed_bindings(bindings: &TypedBindings) {
    for group in &bindings.groups {
        for binder in &group.binders {
            verify_pattern(&binder.pattern);
        }
        verify_expression(&group.ty);
    }
}

#[cfg(debug_assertions)]
fn verify_constructor(ctor: &Constructor) {
    verify_id(&ctor.name);
    verify_expression(&ctor.ty);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_valid_program() {
        // Create a simple valid program
        let def = Def::new(
            0..10,
            Id::new(0..3, "foo".into()),
            Bindings::new(vec![]),
            None,
            Box::new(Expression::Num(Num::new(0..1, "1".into()))),
        );

        let program = Program::new(vec![Statement::Def(def)]);

        // Should not panic
        verify_program(&program);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "App expression must have at least 2 elements")]
    fn test_verify_invalid_app() {
        // Create an App with only 1 element (invalid!)
        let app = App::new(
            0..5,
            vec![Box::new(Expression::Num(Num::new(0..1, "1".into())))],
        );

        verify_expression(&Expression::App(app));
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Identifier must not be empty")]
    fn test_verify_empty_id() {
        let id = Id::new(0..0, "".into());
        verify_id(&id);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Identifier should not be the error marker")]
    fn test_verify_error_marker_id() {
        let id = Id::new(0..7, "<error>".into());
        verify_id(&id);
    }
}
