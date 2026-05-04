# Elaboration Error Messages Research

**Date:** 2026-05-03  
**Topic:** How to produce high-quality error messages from elaboration/type inference  
**Related:** [[decisions/ADR-005-debug-information]], [[entities/bidirectional-typing]]

---

## Executive Summary

Producing good error messages during elaboration/type inference is a **well-researched problem** with modern solutions. The key insight: **error messages should NOT be generated at the first point of failure**, but rather should be diagnosed globally by analyzing the constraint graph with provenance tracking.

### Key Findings

1. **Track constraint origins, not just constraints** - Every constraint needs metadata about WHY it was created
2. **Global diagnosis beats local failure** - Analyze all constraints together to find the "real" error
3. **Metavariable origin tracking is ESSENTIAL** - Users need to know "why was ?m created?"
4. **Data flow explanations work best** - Explain errors as "value flows from X to Y, but types don't match"
5. **Modern compilers do this** - Rust, GHC, Lean 4 all track origins extensively

---

## The Problem: Why Are Type Errors Hard?

### The "Wrong Location" Problem

**Traditional elaborators (Algorithm W, bidirectional typing) report errors at the first failure point:**

```
def foo : Nat -> Bool = λ x => x + 1

Error at line 1, column 32:
  Expected: Bool
  Actual: Nat
```

**But this is misleading!** The actual error is in the type signature (`Bool` should be `Nat`), not in the body.

### Why This Happens

1. **Non-local constraints** - A constraint from line 10 may fail because of code at line 3
2. **Propagation delay** - Errors detected far from their source (especially with metavariables)
3. **Implementation bias** - Error location depends on traversal order, not actual cause
4. **Metavariable opacity** - Users see `?m` but don't know why it exists or what constrains it

### Example from Agda (Issue #2073)

User writes:
```agda
f : {A : Set} -> List A -> Nat
f xs = length (map id xs)
```

Agda reports:
```
Cannot solve metavariable _252
```

**Unhelpful!** What the user needs to know:
- _252 was created as an implicit type argument to `map`
- It couldn't be unified because `xs` was pruned from its scope
- The *actual* fix is to add an explicit type annotation

---

## Solution 1: Constraint Origin Tracking

### Core Idea

**Every constraint must carry metadata about its origin:**

```rust
pub struct Constraint<'db> {
    pub kind: ConstraintKind,           // What constraint (unify, subtype, etc.)
    pub source: SourceLocation<'db>,    // WHERE in source code
    pub origin: ConstraintOrigin,       // WHY it was created
}

pub enum ConstraintOrigin {
    FunctionApplication { function: Span, argument: Span },
    PatternMatch { scrutinee: Span, pattern: Span },
    ReturnType { function_sig: Span, return_expr: Span },
    ImplicitArgument { function: Span, param_index: usize },
    Annotation { expr: Span, annotation: Span },
    // ... many more
}
```

### How Rust Does It

**Rust's `ObligationCause` and `TypeTrace`:**

```rust
pub struct ObligationCause<'tcx> {
    pub span: Span,
    pub body_id: HirId,
    pub code: ObligationCauseCode<'tcx>,  // The "origin"
}

pub enum ObligationCauseCode<'tcx> {
    FunctionArgumentObligation { .. },
    MethodReceiver,
    ReturnNoExpression,
    AssignmentLhsNotStatic,
    // ... 50+ variants
}
```

**Example error message:**
```
error[E0308]: mismatched types
  --> src/main.rs:5:13
   |
5  |     foo(42, "hello");
   |         ^^ expected `&str`, found integer
   |
note: function defined here
  --> src/main.rs:1:4
   |
1  | fn foo(x: &str, y: &str) { }
   |    ^^^    -----
```

The error message points to:
1. Where the mismatch occurred (argument `42`)
2. WHY the type was expected (`&str` from function signature)
3. WHERE the expectation came from (function definition line 1)

### How Lean 4 Does It

**Lean's `SyntheticMVarKind` and error contexts:**

```lean
inductive SyntheticMVarKind where
  | typeClass
  | coe (f? : Option Expr) (header? : Option String)
  | tactic (tacticCode : Syntax)
  | postponed (savedCtx : SavedContext)
```

When a metavariable can't be solved, Lean knows:
- It's for typeclass resolution → suggest instance
- It's for coercion → show expected vs actual types with data flow
- It's from a tactic → show tactic state
- It was postponed → show what info is still needed

---

## Solution 2: Global Error Diagnosis

### The Constraint Graph Approach

Instead of failing at first error, **collect ALL constraints, then diagnose**:

```
1. Collect constraints with origins
2. Attempt to solve (unification/subtyping)
3. IF unsatisfiable:
   a. Build constraint graph
   b. Find unsatisfiable subset(s)
   c. Rank error sources by likelihood
   d. Report most likely cause with full provenance
```

### Research: SHErrLoc (Cornell, 2012)

**Key innovation:** Use satisfiability analysis on constraint graph

```
Given constraints C = {c1, c2, ..., cn} with locations L = {l1, l2, ..., ln}

If C is unsatisfiable:
  1. Find minimal unsatisfiable subset M ⊆ C
  2. Report locations corresponding to M
  3. Use Bayesian ranking: P(li is error | C unsatisfiable)
```

**Example:**

```ocaml
let f x = x + 1 in
let y = "hello" in
f y
```

Constraints:
- c1: x : α  (origin: function parameter)
- c2: α ~ int  (origin: + operator requires int)
- c3: y : string  (origin: literal)
- c4: y : α  (origin: function application)

Minimal unsatisfiable subset: {c2, c3, c4}
→ Report: "f expects int (from +), but called with string"

### Research: Flow-Based Errors (Tübingen, 2024)

**Key innovation:** Explain errors as **data flow paths**

Instead of:
```
Type mismatch: expected int, got string
```

Show:
```
error: value flows to incompatible type
  ┌─ example.ml:3:1
  │
1 │ let f x = x + 1 in
  │           ----- x flows to (+), which requires int
2 │ let y = "hello" in
  │         ------- y has type string
3 │ f y
  │   ^ string flows into int context
  │
  = help: the flow path is: y (string) → f → x (int)
```

Users understand **data flow** better than abstract type constraints!

---

## Solution 3: Metavariable Provenance

### What Information to Track

For every metavariable `?m`, track:

```rust
pub struct MetaVarInfo<'db> {
    pub id: MetaId,
    pub ty: Type<'db>,
    
    // ESSENTIAL for error messages:
    pub created_at: SourceLocation<'db>,
    pub created_by: MetaOrigin,
    pub constrained_by: Vec<ConstraintWithOrigin<'db>>,
    pub solved_at: Option<SourceLocation<'db>>,
}

pub enum MetaOrigin {
    ImplicitArgument { function: Span, param_name: String, param_index: usize },
    TypeInference { expression: Span, reason: String },
    PlaceholderType { annotation_hole: Span },  // User wrote `_`
    UnificationVariable { equation: Span },
    InstanceSearch { class_name: String, required_at: Span },
}
```

### Example: Agda's Improved Errors

**Before** (Agda issue #2073):
```
Cannot solve metavariable _252
```

**After** (with provenance):
```
error: unsolved metavariable ?α
  ┌─ Example.agda:5:10
  │
5 │   result = map id xs
  │            ^^^ implicit type argument to 'map'
  │
  = note: ?α was created as an implicit argument to 'map'
  = note: ?α must satisfy:
          • ?α ~ A  (from function signature, line 3)
          • xs : List ?α  (from application, line 5)
  = note: cannot solve because 'xs' is not in scope of ?α
  = help: try adding an explicit type annotation: map {A} id xs
```

Now the user understands:
1. **What** the metavariable is (implicit type arg)
2. **Why** it exists (function call to `map`)
3. **What** constrains it (the equations)
4. **Why** it failed (scope issue)
5. **How** to fix it (add annotation)

---

## Solution 4: Justifications (Lean's Approach)

### The Justification System

Lean annotates every constraint with a **justification**:

```lean
structure Constraint where
  lhs : Expr
  rhs : Expr
  justification : Justification
  
inductive Justification where
  | ofEqTrue : Expr → Justification
  | ofType : Expr → Justification → Justification
  | ofApp : Justification → Justification → Justification
  | ofFun : Justification → Justification
  -- ... many more
```

When unification fails, Lean can **replay the justification** to show the user:
```
error: type mismatch
  vector : Fin n → α
  has type
    Fin ?n → ?α
  but is expected to have type
    Fin 5 → Nat
    
  Justification chain:
    1. vector parameter 'n' created at line 3
    2. unified with 5 at line 7 (array index)
    3. vector parameter 'α' created at line 3
    4. unified with Nat at line 8 (arithmetic)
    5. function application at line 10 requires Fin 5 → Nat
```

---

## HWML-Specific Implications

### For ADR-005: What Debug Info Do We Actually Need?

Based on this research, **metavariable origin tracking is NOT just debug info—it's ESSENTIAL for error messages**:

| Information | Purpose | Priority |
|-------------|---------|----------|
| `created_at: Location` | Show user WHERE in source | **CRITICAL** |
| `created_by: MetaOrigin` | Explain WHY it exists | **CRITICAL** |
| `constrained_by: Vec<Constraint>` | Show what equations failed | **HIGH** |
| `solved_at: Option<Location>` | Track when/where solved | MEDIUM |
| Residual computation | For dependent types specifically | MEDIUM |
| Debug views | Nice-to-have | LOW |

**Key insight:** This is not "debug information" in the traditional sense (like DWARF). This is **error reporting infrastructure**.

### Recommended Architecture

```rust
// Core elaboration data (ALWAYS present)
pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub solution: Option<RcTerm<'db>>,
    
    // ERROR REPORTING (always tracked)
    pub created_at: Location<'db>,
    pub created_by: MetaOrigin<'db>,
    pub constraints: Vec<ConstraintWithOrigin<'db>>,
}

pub struct ConstraintWithOrigin<'db> {
    pub constraint: UnificationConstraint<'db>,
    pub source: Location<'db>,
    pub origin: ConstraintOrigin,
}

// OPTIONAL debug info (only with --debug=full)
pub struct MetaDebugInfo<'db> {
    pub unification_trace: Vec<UnificationStep<'db>>,
    pub scope_snapshots: Vec<ScopeSnapshot<'db>>,
    pub instantiation_history: Vec<Instantiation<'db>>,
}
```

**Separation:**
- **Provenance** (created_at, created_by, constraints) → **Always present** → Used for error messages
- **Debug traces** (unification steps, scope snapshots) → **Optional** → Used for elaborator debugging

---

## Modern Best Practices

### 1. Always Track Origins

**DON'T:**
```rust
fn add_constraint(&mut self, lhs: Type, rhs: Type) {
    self.constraints.push((lhs, rhs));
}
```

**DO:**
```rust
fn add_constraint(
    &mut self,
    lhs: Type,
    rhs: Type,
    source: Location<'db>,
    origin: ConstraintOrigin,
) {
    self.constraints.push(Constraint { lhs, rhs, source, origin });
}
```

### 2. Defer Error Reporting

**DON'T** (fail immediately):
```rust
fn unify(&mut self, a: Type, b: Type) -> Result<(), TypeError> {
    if !self.can_unify(a, b) {
        return Err(TypeError::Mismatch { expected: a, actual: b });  // ❌ Lost context!
    }
}
```

**DO** (collect, then diagnose):
```rust
fn check_program(&mut self, program: Program) -> Result<(), Vec<ElabError>> {
    // 1. Collect all constraints
    for decl in program.decls {
        self.elaborate_decl(decl)?;  // Adds to self.constraints
    }
    
    // 2. Solve constraints
    match self.solve_constraints() {
        Ok(solution) => Ok(()),
        Err(unsatisfiable) => {
            // 3. Diagnose with full context
            let errors = self.diagnose_errors(unsatisfiable);
            Err(errors)
        }
    }
}
```

### 3. Use Rich Origin Types

**Minimal origins** (like Hindley-Milner):
```rust
pub enum Origin {
    Expression(Span),
}
```

**Rich origins** (like Rust/Lean):
```rust
pub enum ConstraintOrigin {
    FunctionApplication {
        function_name: String,
        function_span: Span,
        argument_index: usize,
        argument_span: Span,
    },
    PatternMatch {
        scrutinee_ty: Type,
        scrutinee_span: Span,
        pattern_span: Span,
    },
    ReturnType {
        declared_ty: Type,
        declared_span: Span,
        returned_expr: Span,
    },
    ImplicitArgument {
        function_name: String,
        param_name: String,
        param_index: usize,
        call_site: Span,
    },
    FieldAccess {
        struct_name: String,
        field_name: String,
        access_span: Span,
    },
    // ... 20-30 more variants
}
```

More detailed origins = better error messages!

### 4. Show Constraint Chains

When a metavariable can't be solved, show the constraint chain:

```
error: cannot solve metavariable ?n
  ┌─ Counter.hwml:10:5
  │
10│   val replicate n false
  │       ^^^^^^^^^ requires implicit argument ?n : Nat
  │
  = note: ?n is constrained by:
    • ?n ~ 8         (from literal at line 12)
    • ?n ~ width(x)  (from field access at line 15)
    • width(x) ~ 16  (from type annotation at line 3)
  = note: conflicting constraints: 8 ≠ 16
  = help: check the width annotation at line 3
```

---

## Comparative Analysis

| System | Origin Tracking | Global Diagnosis | Metavar Provenance | Error Quality |
|--------|----------------|------------------|-------------------|---------------|
| **Algorithm W** | None | No | No | ⭐ Poor |
| **OCaml (classic)** | Spans only | No | No | ⭐⭐ Fair |
| **GHC (Haskell)** | Yes (CtOrigin) | Yes (constraint solver) | Partial | ⭐⭐⭐⭐ Good |
| **Rust (rustc)** | Yes (ObligationCause) | Yes (trait solver) | Yes (TypeVarOrigin) | ⭐⭐⭐⭐⭐ Excellent |
| **Lean 4** | Yes (Justifications) | Yes (elaborator) | Yes (SyntheticMVar) | ⭐⭐⭐⭐⭐ Excellent |
| **Agda** | Yes | Yes | Improving | ⭐⭐⭐⭐ Good |
| **Idris 2** | Yes | Yes | Yes | ⭐⭐⭐⭐ Good |

**Trend:** Modern type systems ALL track origins extensively.

---

## Key Takeaway for HWML

### Metavariable origin tracking is NOT optional debug info

It's **essential error reporting infrastructure** that should ALWAYS be present, regardless of debug flags.

**Recommendation:**

```rust
// ALWAYS present (even in --debug=none mode):
pub struct MetaEntry<'db> {
    pub created_at: Location<'db>,       // For error messages
    pub created_by: MetaOrigin<'db>,     // For error messages
    pub constraints: Vec<ConstraintWithOrigin<'db>>,  // For error messages
}

// OPTIONAL (only in --debug=full mode):
pub struct MetaDebugInfo<'db> {
    pub unification_trace: Vec<UnificationStep<'db>>,  // For elaborator debugging
    pub nbe_residuals: Vec<ResidualInfo<'db>>,         // For advanced debugging
}
```

This gives us:
- ✅ Good error messages by default (always track origins)
- ✅ Optional deep debugging (with --debug=full)
- ✅ No performance penalty for production (no full traces)

---

## References

### Academic Papers

- **Heeren, Hage, Swierstra** (2003): "Scripting the Type Inference Process"
- **Zhang, Myers** (2014): "Toward General Diagnosis of Static Errors" (SHErrLoc)
- **Seidel, Jhala, Weimer** (2016): "Dynamic Witnesses for Static Type Errors"
- **Loncaric, Torlak, Ernst** (2016): "Fast Error Localization via MaxSMT"
- **Pavlinovic, King, Wies** (2015): "Finding Minimum Type Error Sources"
- **Raghu, Bhanuka, Trieu, Chin** (2024): "Getting into the Flow: Towards Better Type Error Messages" (POPL 2024)

### Production Systems

- **Rust** `rustc_trait_selection::error_reporting` - [Source](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_trait_selection/error_reporting/)
- **Lean 4** Elaboration - [Docs](https://lean-lang.org/doc/reference/Elaboration-and-Compilation/)
- **Agda** Issue #2073 - [Discussion](https://github.com/agda/agda/issues/2073)
- **GHC** CtOrigin system - [Wiki](https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/compiler/type-checker)

### Related HWML Docs

- [[decisions/ADR-005-debug-information]] - Debug information strategy
- [[entities/bidirectional-typing]] - Type checking algorithm
- [[entities/pattern-unification]] - Metavariable solving
