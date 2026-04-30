/// Filecheck-style snapshot tests: surface string → parse + elab → core IR string.
///
/// Run with `cargo test -p hwml_elab --test snap_tests`.
/// Accept new snapshots with `cargo insta review` or `INSTA_UPDATE=always cargo test`.
use hwml_core::{val::GlobalEnv, Database};
use hwml_elab::{
    ctx::ElabCtx,
    elab::{decl::elab_constant, Elaborator},
    resolver::Resolver,
    state::SolverState,
    stub_table::StubTable,
    zonk::{substitute_metas_in_syntax, zonk},
};
use hwml_surface::syntax::Statement;

// ─── Helpers ─────────────────────────────────────────────────────────────────

/// Full pipeline: surface string → formatted core IR (or error).
///
/// Each `def` in the input is elaborated independently. Output lines:
///   -- <name>
///   type: <core IR>
///   value: <core IR>
fn elab_str(input: &str) -> String {
    let db = Database::new();
    let global = GlobalEnv::new();

    let program = match hwml_surface::parsing::parse(input.as_bytes()) {
        Some(p) => p,
        None => return "error: parse failed\n".to_string(),
    };

    let mut out = String::new();

    // Create empty resolver and stub table for isolated test elaboration
    let resolver = Resolver::new();
    let stub_table = StubTable::new();

    for stmt in &program.statements {
        match stmt {
            Statement::Def(def) => {
                let name = String::from_utf8_lossy(&def.id.value).into_owned();
                let mut state = SolverState::new();
                let ctx = ElabCtx::empty();
                let mut elab = Elaborator::new(&global, ctx, &mut state, &resolver, &stub_table);

                match elab_constant(&db, &mut elab, def) {
                    Ok(c) => {
                        // Solver already ran inside elab_constant; run zonk to resolve universe metas.
                        match zonk(&mut state) {
                            Ok(()) => {}
                            Err(e) => {
                                out.push_str(&format!("-- {name}\nerror (zonk): {e:?}\n\n"));
                                continue;
                            }
                        }
                        let ty_clean = substitute_metas_in_syntax(&c.ty, &state);
                        let val_clean = substitute_metas_in_syntax(&c.value, &state);
                        let ty_str = hwml_core::syn::print::print_syntax_to_string(&db, &ty_clean);
                        let val_str =
                            hwml_core::syn::print::print_syntax_to_string(&db, &val_clean);
                        out.push_str(&format!("-- {name}\ntype:  {ty_str}\nvalue: {val_str}\n\n"));
                    }
                    Err(e) => {
                        out.push_str(&format!("-- {name}\nerror: {e:?}\n\n"));
                    }
                }
            }
            _ => {}
        }
    }

    out
}

// ─── Snapshot tests ───────────────────────────────────────────────────────────
//
// Ordered by complexity; earlier tests should pass before later ones matter.

// ── Level 0: trivial ─────────────────────────────────────────────────────────

#[test]
fn snap_type_universe() {
    // Bare `Type` annotated as `Type`.
    let src = "def u : Type := Type";
    insta::assert_snapshot!(elab_str(src), @r###"
    -- u
    type:  𝒰0
    value: 𝒰0
    "###);
}

#[test]
fn snap_return_type_binder() {
    // Single typed binder, return it as a type.
    let src = "def id_type (A : Type) : Type := A";
    insta::assert_snapshot!(elab_str(src), @r###"
    -- id_type
    type:  ∀ (%0 : 𝒰0) → 𝒰0
    value: λ %0 → %0
    "###);
}

// ── Level 1: identity / const ─────────────────────────────────────────────────

#[test]
fn snap_identity_function() {
    let src = "def id (A : Type) (a : A) : A := a";
    insta::assert_snapshot!(elab_str(src), @r#"
-- id
type:  ∀ (%0 : 𝒰0) → ∀ (%1 : %0) → %1
value: λ %0 %1 → %0
"#);
}

// ── Level 2: higher-order ─────────────────────────────────────────────────────

#[test]
fn snap_apply() {
    // Function application: (A → B) applied to A gives B.
    let src = "def apply (A : Type) (B : Type) (f : A -> B) (a : A) : B := f a";
    insta::assert_snapshot!(elab_str(src), @r###"
    -- apply
    type:  ∀ (%0 : 𝒰0) → ∀ (%1 : 𝒰0) → ∀ (%2 : ∀ (%2 : %1) → %1) → ∀ (%3 : %2) → %2
    value: λ %0 %1 %2 %3 → 𝒰0
    "###);
}

#[test]
fn snap_const() {
    let src = "def const (A : Type) (B : Type) (a : A) (b : B) : A := a";
    insta::assert_snapshot!(elab_str(src), @r###"
    -- const
    type:  ∀ (%0 : 𝒰0) → ∀ (%1 : 𝒰0) → ∀ (%2 : %1) → ∀ (%3 : %1) → %3
    value: λ %0 %1 %2 %3 → %1
    "###);
}

// ── Level 3: composition ──────────────────────────────────────────────────────

#[test]
fn snap_compose() {
    let src = "def compose (A : Type) (B : Type) (C : Type) (f : B -> C) (g : A -> B) (a : A) : C := f (g a)";
    insta::assert_snapshot!(elab_str(src), @r###"
    -- compose
    type:  ∀ (%0 : 𝒰0) → ∀ (%1 : 𝒰0) → ∀ (%2 : 𝒰0) → ∀ (%3 : ∀ (%3 : %1) → %1) → ∀ (%4 : ∀
    (%4 : %3) → %3) → ∀ (%5 : %4) → %3
    value: λ %0 %1 %2 %3 %4 %5 → 𝒰0
    "###);
}

// ── Level 4: flip (dependent binder types) ────────────────────────────────────

#[test]
fn snap_flip_function() {
    let src =
        "def flip (A : Type) (B : Type) (C : Type) (f : A -> B -> C) (b : B) (a : A) : C := f a b";
    insta::assert_snapshot!(elab_str(src), @r#"
-- flip
type:  ∀ (%0 : 𝒰0) → ∀ (%1 : 𝒰0) → ∀ (%2 : 𝒰0) → ∀ (%3 : ∀ (%3 : %2) → ∀ (%4 : %2) → %2)
→ ∀ (%4 : %2) → ∀ (%5 : %4) → %3
value: λ %0 %1 %2 %3 %4 %5 → 𝒰0
"#);
}

// ── Misc ──────────────────────────────────────────────────────────────────────

#[test]
fn snap_multiple_defs() {
    let src = "\
def id (A : Type) (a : A) : A := a
def const (A : Type) (B : Type) (a : A) (b : B) : A := a";
    insta::assert_snapshot!(elab_str(src), @r#"
-- id
type:  ∀ (%0 : 𝒰0) → ∀ (%1 : %0) → %1
value: λ %0 %1 → %0

-- const
type:  ∀ (%0 : 𝒰0) → ∀ (%1 : 𝒰0) → ∀ (%2 : %1) → ∀ (%3 : %1) → %3
value: λ %0 %1 %2 %3 → %1
"#);
}

#[test]
fn snap_infer_without_annotation() {
    // No type annotation, value synthesised directly.
    let src = "def u := Type";
    insta::assert_snapshot!(elab_str(src), @r###"
    -- u
    type:  𝒰0
    value: 𝒰0
    "###);
}

#[test]
fn snap_fun_without_annotation_errors() {
    // No annotation + lambda body → CannotInfer (can't synth a Fun).
    let src = "def f := fun a => a";
    insta::assert_snapshot!(elab_str(src), @r###"
    -- f
    error: CannotInfer { span: None }
    "###);
}
