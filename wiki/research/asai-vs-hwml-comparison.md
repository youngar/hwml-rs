# Asai vs HWML: Detailed Comparison & Improvement Recommendations

**Date:** 2026-05-08
**Context:** Phase 4 planning - identifying concrete improvements from Asai review

---

## Executive Summary

**Current HWML Status:** ✅ Strong foundation with constraint provenance and span threading
**Gap:** ❌ Missing elaboration backtrace (call stack of elaboration operations)
**Opportunity:** 🚀 Adopt Asai's trace mechanism with Rust-native RAII pattern

**Key Finding:** Our systems are complementary, not redundant. Asai's elaboration backtrace will significantly enhance our constraint-based provenance.

---

## Side-by-Side Comparison

### Architecture

| Feature | Asai (OCaml) | HWML (Current) | Gap? |
|---------|--------------|----------------|------|
| **Constraint Provenance** | ❌ Not present | ✅ Full (`ConstraintOrigin`) | ➕ HWML Better |
| **Meta Provenance** | ❌ Not present | ✅ Full (`MetaProvenance`) | ➕ HWML Better |
| **Elaboration Backtrace** | ✅ Effect-based | ❌ Not present | ➖ **GAP** |
| **Location Threading** | ✅ Automatic (effects) | ⚠️ Manual passing | ➖ **GAP** |
| **Message Codes** | ✅ Short codes ("E001") | ⚠️ Full names | ➖ **GAP** |
| **Backtrace Display** | ✅ Integrated | ⚠️ Partial | ➖ **GAP** |
| **Side-table Architecture** | N/A | ✅ Zero-overhead | ➕ HWML Better |

---

## Detailed Feature Analysis

### 1. Elaboration Backtrace ⭐ **CRITICAL GAP**

#### Asai Has:
```ocaml
let rec chk (tm : tm) (tp : tp) : unit =
  Reporter.tracef ?loc:tm.loc "when checking it against %a" pp_tp tp @@ fun () ->
  match tm.value, tp with
  | Lam (nm, body), Fun (a, b) -> bind_var nm a @@ fun () -> chk body b
  | _ -> let actual_tp = syn tm in equate tp actual_tp
```

**Error output:**
```
error: type mismatch
  expected type Nat, but got Bool

backtrace:
  when checking it against Nat (at line 10)
  when synthesizing its type (at line 8)
  when checking function body (at line 5)
```

#### HWML Has:
```rust
pub fn check<'a, 'db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
    expected_ty: RcTy<'db>,
) -> Result<Checked<RcSyntax<'db>>, ElabError<'db>> {
    // No tracing! Just direct elaboration
    expr::check(db, elab, expr, expected_ty)
}
```

**Error output:**
```
error: type mismatch at 142..150
  expected: Nat
  got:      Bool
```

**Problem:** User doesn't know *how* we got to that check (what function? what context?).

---

### 2. Location Threading ⭐ **MODERATE GAP**

#### Asai Pattern:
```ocaml
let rec syn (tm : tm) : tp =
  Reporter.trace ?loc:tm.loc "when synthesizing" @@ fun () ->
  match tm.value with
  | Var nm -> lookup nm  (* lookup inherits tm.loc automatically *)
```

- Inner calls automatically inherit location
- No manual passing required
- Effect system handles propagation

#### HWML Pattern:
```rust
pub fn synth<'a, 'db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
    let location = expr_location(db, expr);  // Must extract manually
    match expr {
        Expression::Var(v) => {
            // Must pass location explicitly to error
            elab.kernel.ctx.lookup(&v.ident.text)
                .ok_or_else(|| ElabError::NotInScope {
                    name: v.ident.text.clone(),
                    span: Some(location.clone()),  // Manual threading!
                })
        }
        // ...
    }
}
```

- Every error site must manually pass `location`
- Easy to forget
- Verbose

**Solution:** Store "current elaboration context" in `Elaborator` struct.

---

### 3. Message Codes ⭐ **MINOR GAP**

#### Asai:
```ocaml
module Message = struct
  type t =
    | Type_error        (* E001 *)
    | Unbound_variable  (* E002 *)
    | Scope_error       (* E003 *)

  let short_code = function
    | Type_error -> "E001"
    | Unbound_variable -> "E002"
    | Scope_error -> "E003"
end
```

**Output:** `error[E001]: type mismatch`

#### HWML:
```rust
    // ...
}
```

**Solution:** Add `code()` method to `ElabError`.

---

## Concrete Improvement Recommendations

### Priority 1: Add Elaboration Backtrace (Phase 4)

**Estimated Effort:** 5-7 days
**Impact:** ⭐⭐⭐⭐⭐ Critical for user-facing diagnostics

#### Implementation:

**Step 1:** Add context to `Elaborator`
```rust
pub struct ElabContext<'db> {
    trace_stack: Vec<ElabFrame<'db>>,
    current_location: Option<SourceRange<'db>>,
}

pub struct ElabFrame<'db> {
    description: String,
    location: SourceRange<'db>,
    kind: ElabFrameKind,
}

pub enum ElabFrameKind {
    CheckingExpression,
    SynthesizingType,
    CheckingDefinition { name: String },
    CheckingFunctionApplication,
    CheckingReturnType,
}

pub struct Elaborator<'a, 'db> {
    pub kernel: Kernel<'a, 'db>,
    pub context: ElabContext<'db>,  // NEW!
}
```

**Step 2:** RAII Guard
```rust
pub struct TraceGuard<'a, 'db> {
    context: &'a mut ElabContext<'db>,
}

impl<'a, 'db> Drop for TraceGuard<'a, 'db> {
    fn drop(&mut self) {
        self.context.trace_stack.pop();
    }
}

impl<'db> ElabContext<'db> {
    pub fn trace<'a>(
        &'a mut self,
        desc: impl Into<String>,
        loc: SourceRange<'db>,
        kind: ElabFrameKind,
    ) -> TraceGuard<'a, 'db> {
        self.current_location = Some(loc.clone());
        self.trace_stack.push(ElabFrame {
            description: desc.into(),
            location: loc,
            kind,
        });
        TraceGuard { context: self }
    }

    pub fn snapshot(&self) -> Vec<ElabFrame<'db>> {
        self.trace_stack.clone()
    }
}
```

**Step 3:** Instrument Elaboration
```rust
pub fn check<'a, 'db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
    expected_ty: RcTy<'db>,
) -> Result<Checked<RcSyntax<'db>>, ElabError<'db>> {
    let location = expr_location(db, expr);
    let _guard = elab.context.trace(
        format!("checking expression against {}", format_type(&expected_ty)),
        location.clone(),
        ElabFrameKind::CheckingExpression,
    );

    // Original elaboration logic...
    // _guard automatically pops on return or error
}
```

**Step 4:** Add backtrace to errors
```rust
pub enum ElabError<'db> {
    TypeMismatch {
        expected: RcTy<'db>,
        actual: RcTy<'db>,
        span: Option<SourceRange<'db>>,
        elab_backtrace: Vec<ElabFrame<'db>>,  // NEW!
    },
    // ... other variants get the same
}

// Capture backtrace when creating error:
Err(ElabError::TypeMismatch {
    expected,
    actual,
    span: Some(location),
    elab_backtrace: elab.context.snapshot(),
})
```

**Step 5:** Display integrated backtrace
```rust
impl<'db> Display for ElabError<'db> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Show primary error
        match self {
            TypeMismatch { expected, actual, span, elab_backtrace } => {
                write!(f, "error: type mismatch")?;
                if let Some(s) = span {
                    write!(f, " at {:?}", s.range)?;
                }
                writeln!(f, "\n  expected: {}", format_type(expected))?;
                writeln!(f, "  got:      {}", format_type(actual))?;

                // Show elaboration backtrace
                if !elab_backtrace.is_empty() {
                    writeln!(f, "\nelaboration backtrace:")?;
                    for (i, frame) in elab_backtrace.iter().rev().enumerate() {
                        writeln!(f, "  {}: {} at {:?}",
                            i, frame.description, frame.location.range)?;
                    }
                }
            }
            // ...
        }
        Ok(())
    }
}
```

**Expected Output:**
```
error: type mismatch at 142..150
  expected: Nat
  got:      Bool

elaboration backtrace:
  0: checking expression against Nat at 142..150
  1: checking function return type at 140..155
  2: checking definition 'process' at 135..200
  3: elaborating module '/main' at 1..500
```

---

### Priority 2: Location Inheritance Pattern

**Estimated Effort:** 1-2 days
**Impact:** ⭐⭐⭐ Reduces boilerplate, fewer missing spans

#### Current Problem:
```rust
// Must manually thread location everywhere
let location = expr_location(db, expr);
match expr {
    Expression::Var(v) => {
        elab.kernel.ctx.lookup(&v.ident.text)
            .ok_or_else(|| ElabError::NotInScope {
                name: v.ident.text.clone(),
                span: Some(location.clone()),  // VERBOSE!
            })
    }
}
```

#### Solution:
```rust
impl<'db> ElabContext<'db> {
    pub fn current_location(&self) -> Option<SourceRange<'db>> {
        self.current_location.clone()
    }
}

// In Elaborator:
impl<'a, 'db> Elaborator<'a, 'db> {
    pub fn error_not_in_scope(&self, name: String) -> ElabError<'db> {
        ElabError::NotInScope {
            name,
            span: self.context.current_location(),  // Automatic!
            elab_backtrace: self.context.snapshot(),
        }
    }

    pub fn error_type_mismatch(
        &self,
        expected: RcTy<'db>,
        actual: RcTy<'db>
    ) -> ElabError<'db> {
        ElabError::TypeMismatch {
            expected,
            actual,
            span: self.context.current_location(),  // Automatic!
            elab_backtrace: self.context.snapshot(),
        }
    }
}
```

**Usage:**
```rust
// Before:
let location = expr_location(db, expr);
elab.kernel.ctx.lookup(&v.ident.text)
    .ok_or_else(|| ElabError::NotInScope {
        name: v.ident.text.clone(),
        span: Some(location.clone()),
    })

// After:
elab.kernel.ctx.lookup(&v.ident.text)
    .ok_or_else(|| elab.error_not_in_scope(v.ident.text.clone()))
```

**Benefits:**
- ✅ Location automatically inherited from trace guard
- ✅ Backtrace automatically captured
- ✅ Less verbose
- ✅ Harder to forget

---

### Priority 3: Error Codes

**Estimated Effort:** 1 day
**Impact:** ⭐⭐ Better documentation, easier to track

#### Implementation:

```rust
impl<'db> ElabError<'db> {
    pub fn code(&self) -> &'static str {
        match self {
            ElabError::TypeMismatch { .. } => "E001",
            ElabError::NotInScope { .. } => "E002",
            ElabError::CannotInfer { .. } => "E003",
            ElabError::UnificationFailure { .. } => "E004",
            ElabError::OccursCheck { .. } => "E005",
            ElabError::ScopeViolation { .. } => "E006",
            ElabError::UnsolvedMeta { .. } => "E007",
            ElabError::MetaAlreadySolved { .. } => "E008",
            ElabError::NotImplemented { .. } => "E999",
        }
    }

    pub fn severity(&self) -> Severity {
        match self {
            ElabError::NotImplemented { .. } => Severity::Warning,
            _ => Severity::Error,
        }
    }
}

pub enum Severity {
    Error,
    Warning,
    Info,
}
```

**Update Display:**
```rust
impl<'db> Display for ElabError<'db> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "error[{}]: ", self.code())?;
        // ... rest of formatting
    }
}
```

**Output:**
```
error[E001]: type mismatch at 142..150
  expected: Nat
  got:      Bool
```

**Documentation:**
Create `docs/error-codes.md`:
```markdown
# HWML Error Codes

## E001: Type Mismatch
The type checker expected one type but found another.

### Examples:
...

## E002: Name Not In Scope
A variable or definition was referenced but not found in the current scope.

### Examples:
...
```

---

### Priority 4: Unified Display with Both Backtraces

**Estimated Effort:** 1 day
**Impact:** ⭐⭐⭐⭐ Complete diagnostic story

#### Current State:
- `UnsolvedMeta` shows constraint backtrace
- Other errors don't show any backtrace
- No elaboration context

#### Goal:
```
error[E007]: unsolved metavariable ?42 at 100..101

elaboration backtrace:
  0: checking return type at 100..101
  1: checking function 'compute' at 95..105
  2: elaborating module '/main' at 1..500

constraint context:
  origin: underscore placeholder
  created by: C10 (type annotation at 100..101)
  blocking: C10, C15, C20
  parent meta: ?40

provenance chain:
  ?42 <- created from underscore at 100..101
  ?40 <- parameter type inference at 95..100
```

#### Implementation:
```rust
impl<'db> Display for ElabError<'db> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // 1. Error code and primary message
        write!(f, "error[{}]: ", self.code())?;
        self.format_primary_message(f)?;

        // 2. Elaboration backtrace (for ALL errors)
        if let Some(bt) = self.elab_backtrace() {
            self.format_elab_backtrace(f, bt)?;
        }

        // 3. Constraint context (for constraint-related errors)
        if let Some(ctx) = self.constraint_context() {
            self.format_constraint_context(f, ctx)?;
        }

        // 4. Provenance chain (for meta-related errors)
        if let Some(prov) = self.provenance_chain() {
            self.format_provenance_chain(f, prov)?;
        }

        Ok(())
    }
}
```

---

## Performance Analysis

### Asai's Approach
- **Cost:** Nearly zero (effect handlers are compile-time)
- **Allocation:** Only on error
- **Overhead:** None in success case

### HWML Current
- **Cost:** Zero (side-table cleared after elaboration)
- **Allocation:** Only `HashMap` entries on meta creation
- **Overhead:** Hash lookups only

### HWML with Phase 4
- **Cost:** Low (`Vec::push`/`Vec::pop` are ~2 instructions)
- **Allocation:** Stack frames allocated eagerly, but small
- **Overhead:** ~10-20 cycles per elaboration function call

**Optimization opportunities:**
1. Use `SmallVec` for trace stack (avoid heap allocation for shallow traces)
2. Lazy description formatting (only call `format!` on error)
3. Clear trace stack after successful elaboration

```rust
pub struct ElabFrame<'db> {
    description: LazyDescription<'db>,  // Fn() -> String
    location: SourceRange<'db>,
    kind: ElabFrameKind,
}

enum LazyDescription<'db> {
    Static(&'static str),
    Dynamic(Box<dyn Fn() -> String + 'db>),
}

impl<'db> ElabFrame<'db> {
    pub fn description(&self) -> String {
        match &self.description {
            LazyDescription::Static(s) => s.to_string(),
            LazyDescription::Dynamic(f) => f(),
        }
    }
}
```

---

## Migration Strategy

### Phase 4.1: Infrastructure (Week 1)
- [ ] Create `ElabContext` struct
- [ ] Add `TraceGuard` RAII utility
- [ ] Add `context` field to `Elaborator`
- [ ] Add `elab_backtrace` field to all `ElabError` variants

### Phase 4.2: Instrumentation (Week 1-2)
- [ ] Wrap `check()` with trace
- [ ] Wrap `synth()` with trace
- [ ] Wrap definition elaboration
- [ ] Wrap module elaboration

### Phase 4.3: Error Construction (Week 2)
- [ ] Add error helper methods to `Elaborator`
- [ ] Update all `Err(ElabError::...)` sites to use helpers
- [ ] Test that backtraces are captured

### Phase 4.4: Display (Week 2)
- [ ] Add error codes to `ElabError`
- [ ] Update `Display` to show elaboration backtrace
- [ ] Integrate with existing constraint backtrace display

### Phase 4.5: Testing (Week 3)
- [ ] Add backtrace assertions to existing tests
- [ ] Create integration tests for complex errors
- [ ] Document error codes

---

## Comparison Summary

| Feature | Asai | HWML Current | HWML + Phase 4 |
|---------|------|--------------|----------------|
| Constraint Provenance | ❌ | ✅ | ✅ |
| Meta Provenance | ❌ | ✅ | ✅ |
| Elaboration Backtrace | ✅ | ❌ | ✅ |
| Location Inheritance | ✅ | ❌ | ✅ |
| Error Codes | ✅ | ❌ | ✅ |
| Unified Display | ✅ | ⚠️ | ✅ |
| Zero Overhead | ✅ | ✅ | ⚠️ (small) |
| Effect Handlers | ✅ | ❌ | ❌ (RAII) |

**Result:** HWML will have **superior diagnostics** by combining:
- Asai's elaboration backtrace
- HWML's unique constraint/meta provenance
- Rust's RAII safety guarantees

---

## Conclusion

**Recommendation:** Proceed with all 4 priorities:

1. **P1 (Critical):** Elaboration Backtrace - 5-7 days
2. **P2 (High):** Location Inheritance - 1-2 days
3. **P3 (Medium):** Error Codes - 1 day
4. **P4 (High):** Unified Display - 1 day

**Total effort:** ~2-3 weeks for complete diagnostic overhaul

**Expected outcome:** Best-in-class diagnostics that combine:
- Elaboration call stack (from Asai)
- Constraint/meta provenance (unique to HWML)
- Type flow information (from `ConstraintOrigin`)
- Source locations (already complete)

This will put HWML's error messages on par with or exceeding Rust, GHC, and Lean.

**Output:** `error: type mismatch at 142..150`

**Missing:**
- No error codes
- Can't Google for "HWML E001"
- Hard to track error types across versions

**Solution:** Add `code()` method to `ElabError`.

---

## Concrete Improvement Recommendations

### Priority 1: Add Elaboration Backtrace (Phase 4)

**Estimated Effort:** 5-7 days
**Impact:** ⭐⭐⭐⭐⭐ Critical for user-facing diagnostics

#### Implementation:

**Step 1:** Add context to `Elaborator`
```rust
pub struct ElabContext<'db> {
    trace_stack: Vec<ElabFrame<'db>>,
    current_location: Option<SourceRange<'db>>,
}

pub struct ElabFrame<'db> {
    description: String,
    location: SourceRange<'db>,
    kind: ElabFrameKind,
}

pub enum ElabFrameKind {
    CheckingExpression,
    SynthesizingType,
    CheckingDefinition { name: String },
    CheckingFunctionApplication,
    CheckingReturnType,
}

pub struct Elaborator<'a, 'db> {
    pub kernel: Kernel<'a, 'db>,
    pub context: ElabContext<'db>,  // NEW!
}
```

**Step 2:** RAII Guard
```rust
pub struct TraceGuard<'a, 'db> {
    context: &'a mut ElabContext<'db>,
}

impl<'a, 'db> Drop for TraceGuard<'a, 'db> {
    fn drop(&mut self) {
        self.context.trace_stack.pop();
    }
}

impl<'db> ElabContext<'db> {
    pub fn trace<'a>(
        &'a mut self,
        desc: impl Into<String>,
        loc: SourceRange<'db>,
        kind: ElabFrameKind,
    ) -> TraceGuard<'a, 'db> {
        self.current_location = Some(loc.clone());
        self.trace_stack.push(ElabFrame {
            description: desc.into(),
            location: loc,
            kind,
        });
        TraceGuard { context: self }
    }

    pub fn snapshot(&self) -> Vec<ElabFrame<'db>> {
        self.trace_stack.clone()
    }
}
```

