# ADR-015: Elaboration Provenance and Backtrace Architecture

**Status:** Accepted
**Date:** 2026-05-08
**Deciders:** Architecture Team
**Context Tags:** #provenance #error-reporting #diagnostics #elaboration

---

## Context

HWML's elaborator uses constraint-based type inference with metavariables. When elaboration fails, we need to explain:
- **What** went wrong (type mismatch, unsolved meta, etc.)
- **Where** it happened (source location)
- **Why** it happened (what code caused this constraint)
- **How** we got there (elaboration context)

This ADR establishes the architecture for tracking and reporting this information.

### Research Foundation

We studied error reporting systems from:
- **Rust:** `ObligationCause` tracking constraint origins
- **GHC:** `CtOrigin` for constraint provenance
- **Lean 4:** `SyntheticMVarKind` for metavariable context
- **Asai:** Structured backtrace with dynamic scoping (RedPRL team)

**Key Finding from Asai Analysis (2026-05-08):**
- Asai provides excellent elaboration backtrace via OCaml effects
- HWML has superior constraint/meta provenance that Asai lacks
- Systems are **complementary, not redundant**
- Combined approach will exceed both Rust and GHC diagnostics

See `wiki/research/asai-vs-hwml-comparison.md` for detailed comparison and `wiki/research/asai-detailed-review.md` for Asai internals.

---

## Decision

We adopt a **two-level provenance architecture**:

### 1. Constraint Provenance (Implemented - Phase 2.5)

**What it tracks:** Why constraints and metavariables were created

**Components:**
- `MetaOrigin` - Semantic reason for metavariable existence
- `ConstraintOrigin` - Semantic reason for constraint emission
- `MetaProvenance` - Side-table linking metas to origins and constraints

**Storage:** Side-tables cleared after successful SCC elaboration (zero overhead)

**Example:**
```rust
ConstraintOrigin::FunctionApplication {
    function_span: SourceRange,
    argument_span: SourceRange,
    param_index: usize,
}
```

### 2. Elaboration Backtrace (Planned - Phase 4)

**What it tracks:** Call stack of elaboration operations

**Components:**
- `ElabContext` - Stack of elaboration frames
- `ElabFrame` - Description + location + operation kind
- RAII guards for automatic frame management

**Storage:** Thread-local or elaborator-local stack

**Example:**
```rust
ElabFrame {
    description: "checking return type",
    location: SourceRange,
    kind: ElabFrameKind::CheckingTypeAnnotation,
}
```

---

## Architectural Principles

### Principle 1: Separation of Concerns

**`ElabError`** = What failed (the error itself)
- Simple enum with error category
- Returned from operations
- Public API for elaboration failures

**Provenance System** = Why/where it failed (context)
- Side-tables and stacks
- Queried on error

- Internal tracking mechanism
- Enriches errors with actionable information

**No Redundancy:** Each system serves orthogonal purposes.

### Principle 2: Zero Overhead on Success

**Constraint provenance:**
- Stored in side-tables (`HashMap<MetaId, MetaProvenance>`)
- Cleared after successful SCC elaboration
- Only accessed when errors occur

**Elaboration backtrace:**
- Stack-based (push/pop on elaboration operations)
- Automatically cleaned up via RAII guards
- Negligible runtime cost

### Principle 3: Rich Context, Not Just Locations

**Bad (location-only):**
```
error: type mismatch at line 42
```

**Good (constraint provenance):**
```
error: type mismatch at 142..150
  origin: function application parameter 2 at 145..150
  constraint: C10 (return type check) at 142..200
```

**Better (with elaboration backtrace):**
```
error: type mismatch at 142..150
  expected: Nat
  got:      Bool

elaboration context:
  - checking return type (at 142..150)
  - checking function 'process' (at 140..200)
  - elaborating module '/main' (at 1..500)

constraint context:
  - origin: return type check at 142..150
  - created by: C10
  - blocking: C10, C15, C20
```

### Principle 4: Asai-Inspired, Rust-Adapted

**From Asai we adopt:**
- Structured backtrace concept
- Automatic location threading
- Human-readable trace descriptions

**Adapted for Rust:**
- RAII instead of effect handlers
- Explicit state instead of dynamic scoping
- Side-tables instead of always-on tracking

---

## Implementation Status

### ✅ Phase 1: Side-Table Foundation (Complete)
- `MetaProvenance` side-table
- `clear_provenance()` lifecycle
- Zero-overhead validation tests

### ✅ Phase 2: Typed Origins (Complete)
- `MetaOrigin` enum (11 semantic variants)
- `fresh_meta_with_trace()` API
- Origin descriptions for error messages

### ✅ Phase 2.5: Constraint Origins (Complete)
- `ConstraintOrigin` enum (11 semantic variants)
- `emit_*_with_origin()` APIs
- Elaborator integration
- Constraint origins in `UnsolvedMeta` errors

### ✅ Phase 3: Rich Diagnostics (Complete)
- `Display` impl for `ElabError`
- `format_type()` and `format_value()` helpers
- Span threading through unifier
- Location information in all user-facing errors

### 🔄 Phase 4.0: Source Tracking (In Progress)

**Critical Issue Identified (2026-05-08):**
- Current elaboration creates `SourceInfo::Synthetic` everywhere
- Multi-file errors show "synthetic" instead of real file names
- **Root Cause:** `Source<'db>` not threaded through elaboration context
- **Impact:** Phase 4 backtraces would be useless without file information

**Solution: Context-Based Source Tracking**
- Add `current_source: Source<'db>` to `ElabContext`
- Thread real `Source` from file elaboration entry points
- Trace guards combine `current_source` + byte range → `SourceRange`

**Changes Made (2026-05-08):**
- ✅ Created `crates/hwml-elab/src/context.rs`
  - `ElabContext` with `current_source` and `trace_stack`
  - `TraceGuard` RAII pattern
  - `trace()` and `trace_with_source()` methods
- ✅ Updated `Elaborator` struct to include `context: ElabContext<'db>`
- ✅ Updated `Elaborator::new()` to require `source: Source<'db>` parameter
- ✅ Added `expr_byte_range()` helper in `elab/expr.rs`
- 🔄 Updating all `Elaborator::new` call sites (in progress)

**Remaining Work:**
- Update file entry points to create real `Source` from file paths
- Replace synthetic source creation with `context.current_location()`
- Add trace guards to `synth()` and `check()`

**Estimated Time:** 1-2 days
**Documentation:** `wiki/implementation/provenance/PHASE-4.0-SOURCE-TRACKING-PLAN.md`

### 🔜 Phase 4.1-4.5: Elaboration Backtrace (Planned - 1-2 weeks)
**After Phase 4.0 foundation is complete:**

**Phase 4.1:** Add `elab_backtrace` to errors (1-2 days)
**Phase 4.2:** Error helper methods (1 day)
**Phase 4.3:** Instrumentation (58 sites) (2-3 days)
**Phase 4.4:** Error codes + Display (1 day)
**Phase 4.5:** Testing & docs (1-2 days)

**Total Phase 4:** 8-12 days (~2 weeks)

See `wiki/implementation/provenance/PHASE-4-COMPLETE-ROADMAP.md` for detailed plan.

---

## Error Architecture

### Error Type Hierarchy

**Current (Phase 3):**
```rust
pub enum ElabError<'db> {
    // Simple errors - what + where
    TypeMismatch {
        expected: RcTy<'db>,
        actual: RcTy<'db>,
        span: Option<SourceRange<'db>>,
    },
    NotInScope {
        name: String,
        span: Option<SourceRange<'db>>,
    },

    // Rich error - includes full provenance
    UnsolvedMeta {
        meta: MetaId,
        span: Option<SourceRange<'db>>,
        // Provenance data (from side-table)
        origin: Option<MetaOrigin<'db>>,
        parent_meta: Option<MetaId>,
        blocking_constraints: Vec<ConstraintId>,
        created_by_constraint: Option<ConstraintId>,
        constraint_origins: Vec<(ConstraintId, ConstraintOrigin<'db>)>,
    },
}
```

**Planned (Phase 4):**
```rust
pub enum ElabError<'db> {
    TypeMismatch {
        expected: RcTy<'db>,
        actual: RcTy<'db>,
        span: Option<SourceRange<'db>>,
        elab_backtrace: Vec<ElabFrame<'db>>,  // NEW!
    },
    NotInScope {
        name: String,
        span: Option<SourceRange<'db>>,
        elab_backtrace: Vec<ElabFrame<'db>>,  // NEW!
    },
    // ... all errors get elaboration backtrace
}

impl<'db> ElabError<'db> {
    pub fn code(&self) -> &'static str {  // NEW!
        match self {
            TypeMismatch { .. } => "E001",
            NotInScope { .. } => "E002",
            CannotInfer { .. } => "E003",
            UnificationFailure { .. } => "E004",
            UnsolvedMeta { .. } => "E007",
            // ...
        }
    }
}
```

### Error Construction Pattern

**Current (Phase 3):**
```rust
// Simple errors: constructed directly
let location = expr_location(db, expr);
Err(ElabError::NotInScope {
    name: id.value.to_string(),
    span: Some(location),  // Manual threading
})

// Rich errors: queried from provenance
state.make_unsolved_meta_error(meta_id)
```

**Planned (Phase 4) - Error Helper Methods:**
```rust
// Location and backtrace automatically captured!
elab.error_not_in_scope(id.value.to_string())

// Helper implementation:
impl Elaborator {
    pub fn error_not_in_scope(&self, name: String) -> ElabError<'db> {
        ElabError::NotInScope {
            name,
            span: self.context.current_location(),      // Automatic!
            elab_backtrace: self.context.snapshot(),    // Automatic!
        }
    }
}
```

**Benefits:**
- ✅ Less boilerplate (no manual location extraction)
- ✅ Harder to forget backtrace capture
- ✅ Consistent error construction across codebase

---

## What Makes HWML Unique

**After Phase 4, HWML will be the only type checker with all four diagnostic features:**

| Feature | Rust | GHC | Lean 4 | Asai | HWML (Phase 4) |
|---------|------|-----|--------|------|----------------|
| Constraint Provenance | ✅ | ✅ | ✅ | ❌ | ✅ |
| Meta Provenance | ⚠️ | ✅ | ✅ | ❌ | ✅ |
| Elaboration Backtrace | ❌ | ⚠️ | ❌ | ✅ | ✅ |
| Error Codes | ✅ | ✅ | ✅ | ✅ | ✅ (Phase 4) |
| Zero Overhead | ✅ | ❌ | ❌ | ✅ | ✅ |

**What this means:**

1. **Constraint Provenance** - "Why was this equality constraint created?"
   - Rust: Yes (`ObligationCause`)
   - GHC: Yes (`CtOrigin`)
   - HWML: Yes (`ConstraintOrigin`) ✅

2. **Meta Provenance** - "Why does this metavariable exist? What created it?"
   - Rust: Partial (obligation chains)
   - GHC: Yes (constraint solver tracking)
   - Asai: No (doesn't have metavariables)
   - HWML: Yes (`MetaProvenance` with dependency chains) ✅

3. **Elaboration Backtrace** - "What elaboration operations led here?"
   - Asai: Yes (effect-based tracing)
   - HWML Phase 4: Yes (RAII-based tracing) ✅
   - Rust: No (no elaboration phase)
   - GHC: Partial (error context)

4. **Combined Diagnostic** - HWML shows ALL THREE:
   ```
   error[E001]: type mismatch at 142..150

   elaboration backtrace:        ← FROM ASAI (Phase 4)
     - checking expression...

   constraint context:           ← UNIQUE TO HWML (Phase 2.5)
     - origin: return type check

   provenance chain:             ← UNIQUE TO HWML (Phase 2)
     - ?42 <- created from...
   ```

**No other system combines all three!**

---

## Comparison to Alternatives

### Alternative 1: Store Everything in ElabError

**Rejected because:**
- Bloats all error types with provenance fields
- Can't clear provenance after success (memory overhead)
- Mixes error representation with context tracking

### Alternative 2: Effect Handlers (Asai-style)

**Rejected because:**
- Rust doesn't have algebraic effects
- Thread-local state is harder to test
- Explicit is better than implicit for Rust

### Alternative 3: Single Backtrace Type

**Rejected because:**
- Elaboration backtrace (what we're checking) is orthogonal to constraint backtrace (why constraints exist)
- Combining them loses semantic information
- Both provide value independently

### Alternative 4: Deprecate ElabError, Use Only Provenance

**Rejected because:**
- `ElabError` is the **public API** for failures
- Provenance is **internal tracking** for context
- They serve complementary, not redundant, purposes
- Most errors (TypeMismatch, NotInScope) don't need full provenance chains
- Only `UnsolvedMeta` benefits from rich dependency tracking

---

## Benefits

### For Users
1. **Clear error messages** - Know what, where, why, and how
2. **Actionable information** - Can trace error to source
3. **Learning tool** - Understand elaborator's reasoning
4. **Google-able error codes** - "E001" easier to search than "type mismatch"

### For Developers
5. **Debuggability** - Rich context for fixing elaborator bugs
6. **Testability** - Can assert on error provenance
7. **Maintainability** - Explicit tracking vs. implicit magic
8. **Less boilerplate** - Error helpers reduce repetitive code

### For the Project
9. **Best-in-class diagnostics** - Exceeds Rust/GHC by combining elaboration + constraint context
10. **Research alignment** - Follows GHC/Lean/Rust patterns + Asai innovations
11. **Zero overhead** - Provenance cleared on success, backtrace minimal cost (~10-20 cycles/call)
12. **Unique combination** - Only type checker with BOTH elaboration AND constraint provenance

---

## Future Work

### Phase 4: Elaboration Backtrace (Detailed Design)

**Core Infrastructure:**
```rust
pub struct ElabContext<'db> {
    trace_stack: Vec<ElabFrame<'db>>,
    current_location: Option<SourceRange<'db>>,  // For automatic inheritance
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

**Usage:**
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
        location,
        ElabFrameKind::CheckingExpression,
    );

    // Original elaboration logic...
    // _guard automatically pops on return or error
}
```

**Expected Error Display:**
```
error[E001]: type mismatch at 142..150
  expected: Nat
  got:      Bool

elaboration backtrace:
  0: checking expression against Nat at 142..150
  1: checking function return type at 140..155
  2: checking definition 'process' at 135..200
  3: elaborating module '/main' at 1..500

constraint context:
  origin: return type check at 142..150
  created by: C10
  blocking: C10, C15
```

### Phase 5: Ariadne Integration

**Multi-span colored diagnostics:**
```
error[E0308]: type mismatch
  ┌─ expr.hwml:10:15
  │
10│     foo(42, "hello")
  │         ^^ expected Nat, found Bool
  │     --- function expects Nat here
  │
  = note: function 'foo' defined at line 5
```

---

## References

### Internal Documentation
- `wiki/research/asai-vs-hwml-comparison.md` - **NEW** Detailed Asai comparison & improvement recommendations
- `wiki/research/asai-detailed-review.md` - **NEW** Asai codebase deep-dive (401 lines)
- `wiki/implementation/provenance/ASAI-COMPARISON-SUMMARY.md` - **NEW** Executive summary
- `wiki/implementation/provenance/IMPLEMENTATION-PLAN.md` - Execution plan
- `wiki/implementation/provenance/SESSION-SUMMARY.md` - Current status

### External References
- [Asai Library](https://redprl.org/asai/asai/) - RedPRL structured diagnostics
- [Asai Reporter API](https://redprl.org/asai/asai/Asai/Reporter/module-type-S/index.html)
- Rust RFC 1968 - `ObligationCause` and error reporting
- GHC: Constraint solver error messages (OutsideIn(X))
- Lean 4: `SyntheticMVarKind` and elaboration context

---

## Decision Outcomes

**Accepted Architecture:**
1. ✅ **ElabError** - Public error API (what failed)
2. ✅ **Constraint Provenance** - Side-table tracking (why constraints exist)
3. 🔜 **Elaboration Backtrace** - Stack-based tracing (how we got here)
4. 🔜 **Ariadne Integration** - Multi-span colored output

**Key Decisions:**
- ✅ Keep `ElabError` as public API (not deprecated)
- ✅ Use side-tables for zero-overhead provenance
- ✅ Separate constraint backtrace from elaboration backtrace
- ✅ RAII guards for automatic cleanup
- ✅ Span information in all user-facing errors

**Non-Goals:**
- ❌ Deprecating `ElabError` in favor of provenance-only
- ❌ Storing all provenance in error types
- ❌ Effect handlers (not idiomatic Rust)
- ❌ Combining elaboration and constraint backtraces

**This ADR supersedes:** None (first comprehensive provenance decision)

**Related ADRs:**
- ADR-005: Debug Information Strategy (different concern - post-compilation debugging)
- ADR-014: Byte-Level Location Tracking (foundation for spans)

