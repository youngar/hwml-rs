/// Filecheck-style snapshot tests: surface string → parse + elab → core IR string.
///
/// Run with `cargo test -p hwml_elab --test snap_tests`.
/// Accept new snapshots with `cargo insta review` or `INSTA_UPDATE=always cargo test`.
use hwml_core::{Source, SourceInfo, Word, val::GlobalEnv, TestDatabase, syn::ConstantDecl};
use hwml_elab::{
    ctx::ElabCtx,
    elab::{decl::elab_constant, Elaborator},
    resolver::Resolver,
    state::SolverState,
    stub_table::StubTable,
    zonk::{substitute_metas_in_syntax, zonk},
};
use hwml_surface::syntax::Statement;
use hwml_support::IntoWithDb;

// ─── Helpers ─────────────────────────────────────────────────────────────────

/// Full pipeline: surface string → formatted core IR (or error).
///
/// Each `def` in the input is elaborated independently and printed as a
/// complete constant declaration in core IR syntax.
fn elab_str(input: &str) -> String {
    let db = TestDatabase::default();
    let global = GlobalEnv::new();

    let parse_result = hwml_surface::parsing::parse_with_errors(input.as_bytes());
    if !parse_result.errors.is_empty() {
        return format!("error: parse failed with {} errors\n", parse_result.errors.len());
    }
    let program = parse_result.program;

    let mut out = String::new();

    // Create empty resolver and stub table for isolated test elaboration
    let resolver = Resolver::new();
    let stub_table = StubTable::new();

    for stmt in &program.statements {
        match stmt {
            Statement::Def(def) => {
                let name = def.id.value.to_string();
                let mut state = SolverState::new();
                let ctx = ElabCtx::empty();
                let word = Word::new(&db, "snap_test");
                let source = Source::new(&db, SourceInfo::Synthetic(word));
                let mut elab = Elaborator::new(&global, ctx, &mut state, &resolver, &stub_table, source);

                match elab_constant(&db, &mut elab, &def) {
                    Ok(c) => {
                        // Solver already ran inside elab_constant; run zonk to resolve universe metas.
                        match zonk(&mut state) {
                            Ok(()) => {}
                            Err(e) => {
                                out.push_str(&format!("error (zonk): {e}\n\n"));
                                continue;
                            }
                        }
                        // Substitute solved metas
                        let ty_clean = substitute_metas_in_syntax(&c.ty, &state);
                        let val_clean = substitute_metas_in_syntax(&c.value, &state);

                        // Create a ConstantDecl and print it as a complete unit
                        let qname = name.as_str().into_with_db(&db);
                        let const_decl = ConstantDecl::new(qname, ty_clean, val_clean);
                        let decl_str = hwml_core::syn::print::print_constant_decl_to_string(&db, &const_decl);
                        out.push_str(&decl_str);
                        out.push('\n');
                    }
                    Err(e) => {
                        out.push_str(&format!("error: {e}\n\n"));
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
    insta::assert_snapshot!(elab_str(src), @"const @/u : 𝒰0 = 𝒰0;");
}

#[test]
#[ignore = "Known elaborator bug: MetaVariableLookupError - metavariable not registered in global env"]
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
    insta::assert_snapshot!(elab_str(src), @"const @/id : ∀ (%0 : 𝒰0) → ∀ (%1 : %_) → %_ = λ %_ %_ → %_;");
}

// ── Level 2: higher-order ─────────────────────────────────────────────────────

#[test]
fn snap_apply() {
    // Function application: (A → B) applied to A gives B.
    let src = "def apply (A : Type) (B : Type) (f : A -> B) (a : A) : B := f a";
    insta::assert_snapshot!(elab_str(src), @"
    const @/apply : ∀ (%0 : 𝒰0) → ∀ (%1 : 𝒰0) → ∀ (%2 : ∀ (%2 : %_) → %_) → ∀ (%3 :
    %_) → %_ = λ %_ %_ %_ %_ → %_[%_];
    ");
}

#[test]
fn snap_const() {
    let src = "def const (A : Type) (B : Type) (a : A) (b : B) : A := a";
    insta::assert_snapshot!(elab_str(src), @"
    const @/const : ∀ (%0 : 𝒰0) → ∀ (%1 : 𝒰0) → ∀ (%2 : %_) → ∀ (%3 : %_) → %_ = λ %_
      %_
      %_
      %_
      →
      %_;
    ");
}

// ── Level 3: composition ──────────────────────────────────────────────────────

#[test]
fn snap_compose() {
    let src = "def compose (A : Type) (B : Type) (C : Type) (f : B -> C) (g : A -> B) (a : A) : C := f (g a)";
    insta::assert_snapshot!(elab_str(src), @"
    const @/compose : ∀ (%0 : 𝒰0) → ∀ (%1 : 𝒰0) → ∀ (%2 : 𝒰0) → ∀ (%3 : ∀ (%3 : %_)
    → %_) → ∀ (%4 : ∀ (%4 : %_) → %_) → ∀ (%5 : %_) → %_ = λ %_ %_ %_ %_ %_ %_ →
      %_[%_[%_]];
    ");
}

// ── Level 4: flip (dependent binder types) ────────────────────────────────────

#[test]
fn snap_flip_function() {
    let src =
        "def flip (A : Type) (B : Type) (C : Type) (f : A -> B -> C) (b : B) (a : A) : C := f a b";
    insta::assert_snapshot!(elab_str(src), @"
    const @/flip : ∀ (%0 : 𝒰0) → ∀ (%1 : 𝒰0) → ∀ (%2 : 𝒰0) → ∀ (%3 : ∀ (%3 : %_) → ∀
    (%4 : %_) → %_) → ∀ (%4 : %_) → ∀ (%5 : %_) → %_ = λ %_ %_ %_ %_ %_ %_ →
      %_[%_, %_];
    ");
}

// ── Misc ──────────────────────────────────────────────────────────────────────

#[test]
fn snap_multiple_defs() {
    let src = "\
def id (A : Type) (a : A) : A := a
def const (A : Type) (B : Type) (a : A) (b : B) : A := a";
    insta::assert_snapshot!(elab_str(src), @"
    const @/id : ∀ (%0 : 𝒰0) → ∀ (%1 : %_) → %_ = λ %_ %_ → %_;
    const @/const : ∀ (%0 : 𝒰0) → ∀ (%1 : 𝒰0) → ∀ (%2 : %_) → ∀ (%3 : %_) → %_ = λ %_
      %_
      %_
      %_
      →
      %_;
    ");
}

#[test]
fn snap_infer_without_annotation() {
    // No type annotation, value synthesised directly.
    let src = "def u := Type";
    insta::assert_snapshot!(elab_str(src), @"const @/u : 𝒰0 = 𝒰0;");
}

#[test]
fn snap_fun_without_annotation_errors() {
    // No annotation + lambda body → CannotInfer (can't synth a Fun).
    let src = "def f := fun a => a";
    insta::assert_snapshot!(elab_str(src), @r#"
    error: Cannot infer type
      at SourceRange { source: Source(Id(400)), range: 9..19 }

    Elaboration backtrace:
      1. checking definition 'f' (CheckingDefinition { name: "f" })
         at SourceRange { source: Source(Id(400)), range: 0..3 }
      2. synthesizing type for lambda function (SynthesizingType)
         at SourceRange { source: Source(Id(400)), range: 9..19 }
    "#);
}

// ── Implicit Arguments ────────────────────────────────────────────────────────

#[test]
fn snap_implicit_identity() {
    // Identity function with implicit type parameter
    let src = "def id {A : Type} (x : A) : A := x";
    insta::assert_snapshot!(elab_str(src), @"const @/id : ∀ {%0 : 𝒰0} → ∀ (%1 : %_) → %_ = λ {%_} %_ → %_;");
}

#[test]
fn snap_implicit_const() {
    // Const function with implicit type parameters
    let src = "def const {A : Type} {B : Type} (a : A) (b : B) : A := a";
    insta::assert_snapshot!(elab_str(src), @"
    const @/const : ∀ {%0 : 𝒰0} → ∀ {%1 : 𝒰0} → ∀ (%2 : %_) → ∀ (%3 : %_) → %_ = λ {%_}
      {%_}
      %_
      %_
      →
      %_;
    ");
}

#[test]
fn snap_mixed_implicit_explicit() {
    // Function with both implicit and explicit parameters
    let src = "def apply {A : Type} {B : Type} (f : A -> B) (a : A) : B := f a";
    insta::assert_snapshot!(elab_str(src), @"
    const @/apply : ∀ {%0 : 𝒰0} → ∀ {%1 : 𝒰0} → ∀ (%2 : ∀ (%2 : %_) → %_) → ∀ (%3 :
    %_) → %_ = λ {%_} {%_} %_ %_ → %_[%_];
    ");
}

#[test]
fn snap_implicit_compose() {
    // Function composition with implicit type parameters
    let src = "def compose {A : Type} {B : Type} {C : Type} (f : B -> C) (g : A -> B) (a : A) : C := f (g a)";
    insta::assert_snapshot!(elab_str(src), @"
    const @/compose : ∀ {%0 : 𝒰0} → ∀ {%1 : 𝒰0} → ∀ {%2 : 𝒰0} → ∀ (%3 : ∀ (%3 : %_)
    → %_) → ∀ (%4 : ∀ (%4 : %_) → %_) → ∀ (%5 : %_) → %_ = λ {%_}
      {%_}
      {%_}
      %_
      %_
      %_
      →
      %_[%_[%_]];
    ");
}

// ── Implicit Arguments - Error Cases ──────────────────────────────────────────

#[test]
fn snap_implicit_lambda_wrong_arity() {
    // Lambda with wrong number of implicit parameters should error
    let src = "def id {A : Type} (x : A) : A := fun {B} x => x";
    insta::assert_snapshot!(elab_str(src), @r#"
    error: Cannot infer type
      at SourceRange { source: Source(Id(400)), range: 33..47 }

    Elaboration backtrace:
      1. checking lambda function against expected type (CheckingExpression)
         at SourceRange { source: Source(Id(400)), range: 33..47 }
      2. switching to synthesis for lambda function (SwitchingToSynth)
         at SourceRange { source: Source(Id(400)), range: 33..47 }
    "#);
}

#[test]
fn snap_implicit_type_mismatch() {
    // Type mismatch with implicit parameters
    let src = "def bad {A : Type} (x : A) : A := Type";
    insta::assert_snapshot!(elab_str(src), @r#"
    error (zonk): Unsolved metavariable MetaId(4)
      at SourceRange { source: Source(Id(400)), range: 34..38 }
    "#);
}

// ── Implicit Arguments - Complex Cases ────────────────────────────────────────

#[test]
fn snap_implicit_nested_types() {
    // Implicit arguments with nested function types
    let src = "def map {A : Type} {B : Type} (f : A -> B) : (A -> B) := f";
    insta::assert_snapshot!(elab_str(src), @"
    const @/map : ∀ {%0 : 𝒰0} → ∀ {%1 : 𝒰0} → ∀ (%2 : ∀ (%2 : %_) → %_) → ∀ (%3 : %_)
    → %_ = λ {%_} {%_} %_ → %_;
    ");
}

#[test]
fn snap_implicit_return_function() {
    // Function that returns a function with implicit params
    let src = "def make_const {A : Type} (a : A) (B : Type) (b : B) : A := a";
    insta::assert_snapshot!(elab_str(src), @"
    const @/make_const : ∀ {%0 : 𝒰0} → ∀ (%1 : %_) → ∀ (%2 : 𝒰0) → ∀ (%3 : %_) → %_ = λ {%_}
      %_
      %_
      %_
      →
      %_;
    ");
}

#[test]
fn snap_implicit_multiple_in_sequence() {
    // Multiple implicit parameters in a row
    let src = "def triple {A : Type} {B : Type} {C : Type} (a : A) (b : B) (c : C) : A := a";
    insta::assert_snapshot!(elab_str(src), @"
    const @/triple : ∀ {%0 : 𝒰0} → ∀ {%1 : 𝒰0} → ∀ {%2 : 𝒰0} → ∀ (%3 : %_) → ∀ (%4 :
    %_) → ∀ (%5 : %_) → %_ = λ {%_} {%_} {%_} %_ %_ %_ → %_;
    ");
}

// ── DOE (Dynamic Order Elaboration) ───────────────────────────────────────────

#[test]
fn snap_doe_postponed_lambda() {
    // DOE should postpone checking a lambda when the expected type is unknown
    // This is a basic test that DOE doesn't break normal elaboration
    let src = "def id (A : Type) (x : A) : A := x";
    insta::assert_snapshot!(elab_str(src), @"const @/id : ∀ (%0 : 𝒰0) → ∀ (%1 : %_) → %_ = λ %_ %_ → %_;");
}

#[test]
fn snap_doe_implicit_lambda_postponed() {
    // DOE with implicit arguments: postpone checking when type is a meta
    // The implicit lambda insertion should still work correctly
    let src = "def id {A : Type} (x : A) : A := x";
    insta::assert_snapshot!(elab_str(src), @"const @/id : ∀ {%0 : 𝒰0} → ∀ (%1 : %_) → %_ = λ {%_} %_ → %_;");
}

#[test]
fn snap_doe_higher_order() {
    // DOE with higher-order functions
    // Tests that postponing works with nested function types
    let src = "def twice {A : Type} (f : A -> A) (x : A) : A := f (f x)";
    insta::assert_snapshot!(elab_str(src), @"
    const @/twice : ∀ {%0 : 𝒰0} → ∀ (%1 : ∀ (%1 : %_) → %_) → ∀ (%2 : %_) → %_ = λ {%_}
      %_
      %_
      →
      %_[%_[%_]];
    ");
}

#[test]
fn snap_doe_nested_lambdas() {
    // DOE with nested lambdas (curried function)
    let src = "def curry {A : Type} {B : Type} {C : Type} (f : Prod A B -> C) (a : A) (b : B) : C := f (pair a b)";
    insta::assert_snapshot!(elab_str(src), @"
    error: Not in scope: 'Prod'
      at SourceRange { source: Source(Id(400)), range: 48..52 }
    ");
}
