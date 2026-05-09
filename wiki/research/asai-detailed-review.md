# Asai Library - Detailed Code Review

**Date:** 2026-05-08
**Reviewer:** Architecture Team
**Source:** `external/asai/` (local copy from RedPRL)
**Context:** Phase 4 planning - Elaboration backtrace design

---

## Overview

**Asai (浅い "shallow")** is a compiler diagnostics library from the RedPRL team (Jon Sterling et al.), designed for building production-quality error messages in proof assistants and compilers.

**Key Insight:** Uses OCaml's algebraic effects to provide dynamic scoping for backtrace tracking, eliminating the need to explicitly thread context through every function.

---

## Core Architecture

### 1. Effect-Based Dynamic Scoping

**Implementation** (`Reporter.ml:11`):
```ocaml
module Traces = Algaeff.Reader.Make (
  struct type t = Range.t option * Diagnostic.backtrace end
)

let trace_text ?loc text = Traces.scope @@ fun (l, bt) ->
  (match loc with None -> l | Some _ -> loc),
  bt <: {loc; value = text}
```

**How it works:**
- Uses `Algaeff.Reader` (effect-based reader monad)
- Maintains `(current_location, backtrace_stack)` in effect state
- `trace` pushes a frame, runs thunk, automatically pops on exit
- Location automatically threads through nested calls

**Rust equivalent (what we need):**
```rust
// Can't use effects, so use explicit state
struct ElabContext<'db> {
    trace_stack: Vec<ElabFrame<'db>>,
    current_loc: Option<SourceRange<'db>>,
}

impl ElabContext {
    fn trace<T>(&mut self, desc: &str, loc: SourceRange, f: impl FnOnce() -> T) -> T {
        self.trace_stack.push(ElabFrame { desc, loc });
        let result = f();
        self.trace_stack.pop();
        result
    }
}
```

### 2. Message Type System

**Design** (`Reporter_sigs.ml:5-15`):
```ocaml
module type Message =
sig
  type t  (* User-defined message enum *)
  val default_severity : t -> Diagnostic.severity
  val short_code : t -> string  (* "E001", not "type-checking error" *)
end
```

**Principles:**
- Short, Google-able codes (like Rust's `E0308`)
- Severity is property of message type, not error instance
- User defines their own message enum

**HWML equivalent:**
```rust
pub enum ElabMessage {
    TypeMismatch,      // E001
    UnsolvedMeta,      // E002
    NotInScope,        // E003
    // ...
}

impl ElabMessage {
    fn severity(&self) -> Severity {
        match self {
            TypeMismatch | UnsolvedMeta => Severity::Error,
            // ...
        }
    }

    fn code(&self) -> &'static str {
        match self {
            TypeMismatch => "E001",
            UnsolvedMeta => "E002",
            // ...
        }
    }
}
```

### 3. Backtrace Representation

**Structure** (`Diagnostic.ml`):
```ocaml
type backtrace = loctext bwd  (* Backward list *)
type loctext = { loc: Range.t option; value: Text.t }
```

**Key properties:**
- Immutable (functional)
- Snoc list (efficient append)
- Each frame has optional location + text description
- Location inheritance: inner frames inherit outer locations

---

## Usage Patterns (from STLC Example)

### Pattern 1: Tracing Type Checking

**Code** (`Checker.ml:40-41`):
```ocaml
let rec chk (tm : tm) (tp : tp) : unit =
  Reporter.tracef ?loc:tm.loc "when checking it against %a" pp_tp tp @@ fun () ->
  match tm.value, tp with
  | Lam (nm, body), Fun (a, b) ->
      bind_var nm a @@ fun () -> chk body b
  | ...
```

**What this does:**
1. Pushes "when checking it against T" onto backtrace
2. Sets `tm.loc` as current default location
3. Runs the thunk (checking code)
4. Automatically pops frame when done

**Error output includes:**
```
error: type mismatch
  expected: Nat
  got:      Bool

backtrace:
  - when checking it against Nat (at line 10)
  - when synthesizing its type (at line 8)
  - ...
```

### Pattern 2: Nested Tracing


```
error: type mismatch at 142..150
  expected: Nat
  got:      Bool

elaboration backtrace:
  0: checking return type at 142..150
  1: checking function definition 'process' at 140..200
  2: elaborating module '/main' at 1..500

constraint context:
  origin: return type check at 142..150
  created by: C10
  blocking: C10, C15
```

---

## Example Implementation

### Real Example from Asai STLC

**Source** (`Checker.ml:40-63`):
```ocaml
let rec chk (tm : tm) (tp : tp) : unit =
  Reporter.tracef ?loc:tm.loc "when checking it against %a" pp_tp tp @@ fun () ->
  match tm.value, tp with
  | Lam (nm, body), Fun (a, b) ->
      bind_var nm a @@ fun () -> chk body b
  | Pair (l, r), Tuple (a, b) ->
      chk l a;
      chk r b;
  | _ ->
      let actual_tp = syn tm in
      equate tp actual_tp
```

**What this produces:**
```
error: type mismatch
  expected type Nat, but got Bool

backtrace:
  when checking it against Nat (at line 10, column 5)
  when synthesizing its type (at line 8, column 3)
```

### HWML Equivalent (Proposed)

```rust
pub fn check<'a, 'db>(
    db: &'db impl Database,
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
    expected_ty: RcTy<'db>,
) -> Result<RcSyntax<'db>, ElabError<'db>> {
    let location = expr_location(db, expr);
    let _guard = elab.context.trace(
        format!("checking expression against {}", format_type(&expected_ty)),
        location.clone(),
        ElabFrameKind::CheckingExpression,
    );

    match expr {
        Expression::Fun(fun) => {
            match elab.kernel.force_to_pi(expected_ty.clone()) {
                Ok((dom, cod)) => elab.kernel.check_lambda(db, fun, dom, cod),
                Err(_) => {
                    let s = synth(db, elab, expr)?;
                    let origin = ConstraintOrigin::TypeAnnotation {
                        annotation_span: location.clone(),
                        expression_span: location.clone(),
                    };
                    Ok(elab.kernel.expect_with_origin(expected_ty, s, origin, location))
                }
            }
        }
        _ => {
            let s = synth(db, elab, expr)?;
            let origin = ConstraintOrigin::TypeAnnotation {
                annotation_span: location.clone(),
                expression_span: location.clone(),
            };
            Ok(elab.kernel.expect_with_origin(expected_ty, s, origin, location))
        }
    }
    // _guard automatically pops trace frame here
}
```

---

## Error Display Integration

### Add Backtrace to ElabError Display

```rust
impl<'db> Display for ElabError<'db> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Show primary error
        write!(f, "{}", self.format_message())?;

        // Show elaboration backtrace if available
        if let Some(trace) = self.elab_backtrace() {
            writeln!(f, "\nelaboration backtrace:")?;
            for (i, frame) in trace.iter().rev().enumerate() {
                writeln!(f, "  {}: {} at {:?}",
                    i, frame.description, frame.location.range)?;
            }
        }

        // Show constraint backtrace if available (existing code)
        if let ElabError::UnsolvedMeta { origin, constraint_origins, .. } = self {
            writeln!(f, "\nconstraint context:")?;
            // ... existing constraint display code ...
        }

        Ok(())
    }
}
```

---

## Performance Considerations

### Asai's Approach

**Cost:** Nearly zero
- Effect handlers are compile-time transformations
- No runtime allocation unless error occurs
- Backtrace only built when diagnostic is created

**HWML Adaptation:**

**Cost:** Low
- `Vec::push` / `Vec::pop` are cheap
- Only allocate strings on error
- RAII guard is zero-cost abstraction

**Optimization:**
```rust
// Don't allocate description string unless error occurs
pub struct ElabFrame<'db> {
    description: LazyDescription,  // Fn() -> String
    location: SourceRange<'db>,
    kind: ElabFrameKind,
}

// Only call description() when displaying error
```

---

## Testing Strategy

### From Asai Examples

**Test Pattern:**
```ocaml
let () =
  Reporter.run
    ~emit:(fun diag ->
      (* Collect diagnostics for assertion *)
      diagnostics := diag :: !diagnostics)
    ~fatal:(fun diag ->
      (* Handle fatal errors *)
      raise (Fatal diag))
    (fun () ->
      check_term example_term)
```

**HWML Equivalent:**
```rust
#[test]
fn test_elaboration_backtrace() {
    let db = TestDatabase::default();
    let mut elab = Elaborator::new(&db);

    // Run elaboration
    let result = check(&db, &mut elab, bad_expr, expected_ty);

    // Assert error includes backtrace
    match result {
        Err(ElabError::TypeMismatch { elab_backtrace, .. }) => {
            assert!(elab_backtrace.len() >= 2);
            assert!(elab_backtrace[0].description.contains("checking expression"));
            assert!(elab_backtrace[1].description.contains("checking definition"));
        }
        _ => panic!("Expected TypeMismatch error"),
    }
}
```

---

## Migration Path

### Phase 4.1: Infrastructure (1-2 days)

1. Create `ElabContext` with trace stack
2. Add `trace()` method with RAII guard
3. Store context in `Elaborator`
4. Add `elab_backtrace` field to `ElabError` variants

### Phase 4.2: Instrumentation (2-3 days)

1. Wrap `check()` with trace
2. Wrap `synth()` with trace
3. Wrap definition elaboration
4. Wrap constraint solving phases

### Phase 4.3: Display (1 day)

1. Add backtrace to `ElabError::Display`
2. Format as "elaboration backtrace"
3. Distinguish from constraint backtrace

### Phase 4.4: Testing (1 day)

1. Add backtrace assertions to tests
2. Create integration tests with real errors
3. Validate backtrace quality

**Total estimate:** 5-7 days for complete Phase 4

---

## References

- Asai source code: `external/asai/`
- Asai documentation: https://redprl.org/asai/asai/
- STLC example: `external/asai/examples/stlc/Checker.ml`
- Effect handlers: `Algaeff` library
- Related: ADR-015 (Elaboration Provenance Architecture)

---

## Conclusion

**Asai provides an excellent model** for elaboration backtrace, with the caveat that we must adapt effect-based patterns to Rust's RAII idioms.

**Key takeaways:**
1. ✅ Trace stack is valuable and proven
2. ✅ RAII guards can replace effects ergonomically
3. ✅ Location threading reduces boilerplate
4. ✅ Backtrace complements (not replaces) constraint provenance
5. ✅ Implementation is tractable (~1 week)

**Recommendation:** Proceed with Phase 4 implementation following this review's design patterns.
