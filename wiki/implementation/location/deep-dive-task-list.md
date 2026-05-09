# Location Tracking Implementation - Deep Dive Task List

**Date:** 2026-05-05
**Status:** Planning - Ready for Implementation
**Effort:** ~90 hours (~2.5 weeks full-time)

This document contains a comprehensive task list based on a deep dive into the compiler's current location tracking implementation.

---

## Quick Reference

### What This Implements:
1. ✅ **Line:Column native representation** (no more byte offset conversion hell)
2. ✅ **Locations in Core IR** - Every `Syntax` variant carries source location
3. ✅ **Metavariable provenance** - Track where `?123` came from and why
4. ✅ **Constraint origins** - Explain "why are we unifying X and Y?"
5. ✅ **Rich error messages** - Multi-location errors with flow visualization
6. ✅ **LSP integration** - Accurate hover, go-to-def, diagnostics
7. ✅ **CIRCT/MLIR ready** - Emit FileLineColLoc for hardware synthesis

### Implementation Phases:
| Phase | Focus | Hours | Priority |
|-------|-------|-------|----------|
| 1. Foundation | Location type, LineInfo, parser | 9h | **P0 - Blocking** |
| 2. Core IR | Add locations to Syntax enum | 19h | **P0 - Essential** |
| 3. Meta Provenance | Track metavariable origins | 10h | **P1 - High value** |
| 4. Constraint Origins | Track why constraints exist | 8h | **P1 - High value** |
| 5. Error Messages | Rich diagnostics | 17h | **P2 - User-facing** |
| 6. Testing | Verification suite | 23h | **P2 - Quality** |
| 7. Integration | LSP & CIRCT | 7h | **P3 - Polish** |

### Start Here:
1. Read **Phase 1** below (Foundation tasks)
2. Implement **Task 1.1** (Define `Location` type)
3. Implement **Task 1.2** (Extend `LineInfo`)
4. Move to **Phase 2** (Core IR)

---

## Executive Summary

### Current State:
- ✅ **Surface syntax** has `loc: Range<usize>` (byte offsets)
- ✅ **`LineInfo`** utility converts byte offsets ↔ (line, column)
- ✅ **`SourceFileId`** and `SourceRange` exist with byte offset ranges
- ✅ **Errors** have `Option<SourceRange<'db>>` fields
- ❌ **Core IR** (`Syntax` enum) has **NO location fields** in any variant
- ❌ **Metavariables** have **NO provenance tracking** (where created, why)
- ❌ **Constraints** have **NO origin tracking** (why constraint was emitted)
- ❌ **No Line:Column** native representation (still using byte offsets)

### Critical Gaps:
1. **Location loss during elaboration** - Surface syntax locations discarded when creating Core IR
2. **No metavariable provenance** - Cannot explain where `?123` came from or why it exists
3. **No constraint origins** - Cannot explain "why are these two types being unified?"
4. **Byte offset dependency** - Must convert to Line:Column for CIRCT/MLIR, LSP, error reporting

---

## Phase 1: Foundation - Location Type & Infrastructure

### Task 1.1: Define `Location` Type
**File:** `crates/hwml-core/src/source_range.rs`

```rust
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Position {
    pub line: u32,      // 0-based
    pub column: u32,    // 0-based (byte offset within line)
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum LocationData<'db> {
    FileLineColRange {
        file: SourceFileId<'db>,
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
    },
    FileBytesRange {
        file: SourceFileId<'db>,
        start: usize,
        end: usize,
    },
    Synthetic {
        label: Word<'db>,
    },
}

#[salsa::interned]
pub struct Location {
    pub data: LocationData<'db>,
}
```

**Action Items:**
- [ ] Add `Position` struct
- [ ] Add `LocationData` enum with 3 variants
- [ ] Make `Location` a `#[salsa::interned]` type
- [ ] Add conversion methods: `to_line_col()`, `from_byte_range()`
- [ ] Add helper constructors: `Location::file_range()`, `Location::synthetic()`

**Estimated Effort:** 2 hours

---

### Task 1.2: Extend `LineInfo` Integration
**File:** `crates/hwml-support/src/line_info.rs`

**Action Items:**
- [ ] Add `line_col_to_offset(line, col) -> usize` (reverse conversion)
- [ ] Add `validate_position(pos) -> bool` (check if position is valid)
- [ ] Add `span_text(start, end) -> &str` (extract source text for range)
- [ ] Make `LineInfo` available as Salsa tracked query: `line_info(db, file: SourceFile) -> LineInfo`

**Estimated Effort:** 3 hours

---

### Task 1.3: Parser Integration - Convert Byte Offsets to Line:Column
**File:** `crates/hwml-surface/src/parsing.rs`, `crates/hwml-elab/src/elab/expr.rs`

Current parser produces `Range<usize>` (byte offsets). Need to convert immediately.

**Action Items:**
- [ ] Create `ParserContext` struct to hold `LineInfo` during parsing
- [ ] Add `fn byte_range_to_location(db, file, range) -> Location` helper
- [ ] Update all surface syntax creation sites to compute `Location` immediately
- [ ] Keep `Range<usize>` in surface syntax temporarily (for backward compat)
- [ ] Add `location: Location<'db>` field to surface syntax nodes

**Estimated Effort:** 4 hours

---

## Phase 2: Core IR - Add Locations to Every Syntax Variant

### Task 2.1: Add Location Field to All Core `Syntax` Enum Variants
**File:** `crates/hwml-core/src/syn/syntax.rs`

**Current:** No location fields
```rust
pub enum Syntax<'db> {
    Lambda(Lambda<'db>),
    Application(Application<'db>),
    // ...
}
```

**Target:** Every variant carries location
```rust
pub enum Syntax<'db> {
    Lambda(Lambda<'db>, Location<'db>),
    Application(Application<'db>, Location<'db>),
    PiCode(RcSyntax<'db>, BindingSyntax<'db>, Location<'db>),
    // ... ALL 30+ variants
}
```

**Action Items:**
- [ ] Add `Location<'db>` as **last field** to all 30+ enum variants
- [ ] Add `impl Syntax { pub fn location(&self) -> Location<'db> { match self { ... } } }`
- [ ] Update all `Syntax::new()` constructors to require `location` parameter
- [ ] Add `*_with_loc()` helper methods for common cases

**Estimated Effort:** 6 hours (mechanical but needs care with all variants)

---

### Task 2.2: Update All Elaboration Sites to Propagate Locations
**Files:** `crates/hwml-elab/src/elab/expr.rs`, `crates/hwml-elab/src/elab/decl.rs`

When elaborating from Surface → Core, preserve source locations.

**Action Items:**
- [ ] Update `synth()` function - extract location from surface expression, pass to Core constructors
- [ ] Update `check()` function - same location propagation
- [ ] Update `synth_arrow()` - combine source and target locations into Pi location
- [ ] Update `synth_application()` - propagate application site location
- [ ] Update all lambda/pi/let elaboration - preserve locations through transformations
- [ ] **For synthetic terms** (compiler-generated): Use `Location::synthetic(db, "implicit_argument")` etc.

**Example:**
```rust
// Current (no location):
let core_lambda = Syntax::lambda_rc(body);

// Target (with location):
let loc = surface_expr.location(db);  // Extract from surface
let core_lambda = Syntax::lambda_rc(body, loc);
```

**Estimated Effort:** 8 hours

---

### Task 2.3: Verify Location Preservation Transformations
**File:** `crates/hwml-core/src/quote.rs`, `crates/hwml-core/src/eval.rs`

**Action Items:**
- [ ] Update `quote()` function to preserve locations when quoting values → syntax
- [ ] Update `eval()` - locations flow from syntax → values (if we add them to values)
- [ ] **Decision needed**: Should `Value` carry locations? (Probably not - they're semantic)
- [ ] Ensure location is preserved through:
  - [ ] Beta reduction
  - [ ] Pattern matching elaboration
  - [ ] Constraint solving substitutions (zonking)

**Estimated Effort:** 5 hours

---

## Phase 3: Metavariable Provenance Tracking

### Task 3.1: Add Provenance to `MetaEntry`
**File:** `crates/hwml-elab/src/meta.rs`

**Current:**
```rust
pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub arity: usize,
    pub solution: Option<MetaSolution<'db>>,
    pub kind: MetaKind,
}
```

**Target:**
```rust
#[derive(Debug, Clone)]
pub enum MetaOrigin<'db> {
    ImplicitArgument {
        function_loc: Location<'db>,
        param_index: usize,
        param_name: String,
    },
    TypeInference {
        expression_loc: Location<'db>,
        reason: String,  // "cannot infer type for underscore"
    },
    UniverseLevel {
        type_annotation_loc: Location<'db>,
    },
    UnificationVariable {
        equation_loc: Location<'db>,
    },
    PatternSynthesis {
        pattern_loc: Location<'db>,
        constructor: String,
    },
}

pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub arity: usize,
    pub solution: Option<MetaSolution<'db>>,
    pub kind: MetaKind,

    // NEW:
    pub created_at: Location<'db>,
    pub created_by: MetaOrigin<'db>,
    pub constrained_by: Vec<ConstraintId>,  // Track which constraints involve this meta
}
```

**Action Items:**
- [ ] Add `MetaOrigin` enum with 5+ variants
- [ ] Add `created_at`, `created_by`, `constrained_by` fields to `MetaEntry`
- [ ] Update `SolverState::fresh_meta()` to require `origin: MetaOrigin` parameter
- [ ] Update all callsites of `fresh_meta()` (30+ locations) to provide origin

**Estimated Effort:** 6 hours

---

### Task 3.2: Update All `fresh_meta()` Callsites
**Files:** `crates/hwml-elab/src/kernel/mod.rs`, `crates/hwml-elab/src/elab/expr.rs`, etc.

**Action Items:**
- [ ] `synth_universe()` - origin: `UniverseLevel { type_annotation_loc }`
- [ ] `check_underscore()` - origin: `TypeInference { expression_loc, reason: "underscore" }`
- [ ] `synth_application()` - implicit args: `ImplicitArgument { function_loc, param_index, param_name }`
- [ ] Pattern match elaboration - `PatternSynthesis { pattern_loc, constructor }`
- [ ] Anti-unification witness metas - `UnificationVariable { equation_loc }`

**Estimated Effort:** 4 hours

---

## Phase 4: Constraint Origin Tracking

### Task 4.1: Add Origin to Constraints
**File:** `crates/hwml-elab/src/constraint.rs`

**Current:**
```rust
pub enum Constraint<'db> {
    Eq { lhs, rhs, ty, witness, depth },
    LevelLeq { smaller, larger },
    ResolveDot { ... },
}
```

**Target:**
```rust
#[derive(Debug, Clone)]
pub enum ConstraintOrigin<'db> {
    FunctionApplication {
        function_loc: Location<'db>,
        argument_loc: Location<'db>,
        param_index: usize,
    },
    ReturnType {
        declared_loc: Location<'db>,
        returned_loc: Location<'db>,
    },
    PatternMatch {
        scrutinee_loc: Location<'db>,
        pattern_loc: Location<'db>,
        constructor: String,
    },
    FieldAccess {
        record_loc: Location<'db>,
        field_loc: Location<'db>,
        field_name: String,
    },
    TypeAnnotation {
        annotation_loc: Location<'db>,
        expression_loc: Location<'db>,
    },
    InductiveConstructor {
        constructor_loc: Location<'db>,
        type_constructor: String,
    },
    // Add 15-20 more variants for comprehensive coverage
}

pub enum Constraint<'db> {
    Eq {
        lhs, rhs, ty, witness, depth,
        origin: ConstraintOrigin<'db>,  // NEW
    },
    // ...
}
```

**Action Items:**
- [ ] Add `ConstraintOrigin` enum with 20+ rich variants
- [ ] Add `origin: ConstraintOrigin<'db>` to all `Constraint` variants
- [ ] Update `emit_eq()`, `emit_resolve_dot()` to require `origin` parameter
- [ ] Update all constraint emission sites to provide rich origin context

**Estimated Effort:** 8 hours

---

## Phase 5: Error Message Enhancement

### Task 5.1: Update Error Types to Use Location (Not Just SourceRange)
**File:** `crates/hwml-elab/src/error.rs`, `crates/hwml-core/src/check.rs`

**Action Items:**
- [ ] Change `ElabError::TypeMismatch { span: Option<SourceRange> }` → `location: Option<Location>`
- [ ] Add context to errors:
  ```rust
  TypeMismatch {
      expected: RcTy<'db>,
      actual: RcTy<'db>,
      location: Location<'db>,
      context: TypeErrorContext<'db>,  // NEW - rich context
  }
  ```
- [ ] Add `TypeErrorContext` enum:
  ```rust
  enum TypeErrorContext<'db> {
      FunctionApplication { function_loc: Location, arg_index: usize },
      ReturnValue { declared: Location, returned: Location },
      PatternMatch { scrutinee_loc: Location, pattern_loc: Location },
      // 10+ variants
  }
  ```

**Estimated Effort:** 5 hours

---

### Task 5.2: Enhanced Error Reporting with Flow Visualization
**File:** New `crates/hwml-elab/src/diagnostics.rs`

**Action Items:**
- [ ] Create `Diagnostic` type with multiple `Label`s (like Rust's `rustc_errors`)
- [ ] Implement multi-location error rendering:
  ```
  error: type mismatch
    ┌─ adder.hwml:3:5
    │
  1 │ def half_adder (a b : Bit) : Bit × Bit :=
    │                       --- parameter 'a' has type Bit
  2 │   let sum := xor a b in
    │              ^^^^^^^ function 'xor' expects Nat
  3 │   (sum, carry)
    │    ^^^ type error: Bit cannot flow to Nat context
    │
    = help: metavariable ?123 was created for 'xor' application (line 2)
    = note: constraint #45: ?123 = Nat (from function signature)
    = note: constraint #47: ?123 = Bit (from argument 'a' on line 1)
  ```
- [ ] Integrate with `codespan-reporting` crate for LSP-compatible diagnostics
- [ ] Add metavariable origin explanation in error notes
- [ ] Add constraint trace (show chain of unifications that led to error)

**Estimated Effort:** 12 hours

---

## Phase 6: Verification & Testing

### Task 6.1: Location Preservation Tests
**File:** New `crates/hwml-elab/tests/location_tracking.rs`

**Action Items:**
- [ ] Test: Parse → Elab → Core IR preserves line:column exactly
- [ ] Test: Synthetic locations are properly labeled
- [ ] Test: Metavariable created at correct location
- [ ] Test: Constraint originates from correct expression
- [ ] Test: Error points to exact source location
- [ ] Test: Multi-file compilation preserves file identity in locations

**Estimated Effort:** 6 hours

---

### Task 6.2: Metavariable Provenance Tests
**File:** `crates/hwml-elab/tests/meta_provenance.rs`

**Action Items:**
- [ ] Test: Implicit argument meta has correct origin (`ImplicitArgument`)
- [ ] Test: Type inference meta has correct source location
- [ ] Test: Universe level meta traces back to `Type` keyword
- [ ] Test: Anti-unification witness meta links to equation
- [ ] Test: Unsolved meta error shows where it was created and why

**Estimated Effort:** 4 hours

---

### Task 6.3: Constraint Origin Tests
**File:** `crates/hwml-elab/tests/constraint_origins.rs`

**Action Items:**
- [ ] Test: Function application emits constraint with correct origin
- [ ] Test: Return type checking has `ReturnType` origin
- [ ] Test: Pattern match emits constraints with pattern locations
- [ ] Test: Unification failure shows why constraint was created
- [ ] Test: Constraint blocking reports clear reason ("waiting on ?123 created at line 5")

**Estimated Effort:** 5 hours

---

### Task 6.4: End-to-End Error Message Quality Tests
**File:** `crates/hwml-elab/tests/error_quality.rs`

**Action Items:**
- [ ] Test: Type mismatch shows both locations (expected vs actual)
- [ ] Test: Unsolved meta error explains provenance
- [ ] Test: Occurs check error shows cycle with locations
- [ ] Test: Scope violation error shows meta's context vs usage site
- [ ] Golden tests: Snapshot expected error format for regression testing

**Estimated Effort:** 8 hours

---

## Phase 7: LSP & CIRCT Integration

### Task 7.1: LSP Diagnostic Conversion
**File:** `crates/hwml-lsp-server/src/diagnostics.rs`

**Action Items:**
- [ ] Convert `Location<'db>` → `lsp_types::Range`
- [ ] Handle `Position` (0-based) → LSP Position (0-based, but UTF-16 columns!)
- [ ] Add related information for multi-location errors
- [ ] Test with VS Code / Neovim LSP client

**Estimated Effort:** 4 hours

---

### Task 7.2: CIRCT/MLIR Location Emission
**File:** `crates/hwml-circt/src/location.rs` (future)

**Action Items:**
- [ ] Convert `Location<'db>` → MLIR `FileLineColLoc`
- [ ] Handle fused locations for multi-part expressions
- [ ] Emit `loc(unknown)` for synthetic locations
- [ ] Verify CIRCT accepts emitted locations

**Estimated Effort:** 3 hours

---

## Summary & Effort Estimate

### Total Estimated Effort: **~90 hours** (~2.5 weeks full-time)

### Phases:
1. **Foundation** (9 hours) - Location type, LineInfo, parser integration
2. **Core IR** (19 hours) - Add locations to Syntax enum, update elaboration
3. **Metavariable Provenance** (10 hours) - Origin tracking for metas
4. **Constraint Origins** (8 hours) - Rich origin data for constraints
5. **Error Messages** (17 hours) - Enhanced diagnostics with context
6. **Testing** (23 hours) - Comprehensive verification
7. **Integration** (7 hours) - LSP and CIRCT support

### Priority Order (for incremental implementation):
1. **Phase 1** (Foundation) - Blocking for everything else
2. **Phase 2.1** (Core IR locations) - Essential for any error reporting
3. **Phase 3.1** (Meta provenance) - High-value for error messages
4. **Phase 4.1** (Constraint origins) - Completes the error story
5. **Phase 5** (Error messages) - User-visible improvements
6. **Phase 6** (Testing) - Prevent regressions
7. **Phase 2.2, 2.3, 7** (Remaining tasks) - Polish and integration

---

## Critical Verification Points

After each phase, verify:

1. **Location Accuracy:** Locations point to exact source positions
2. **No Location Loss:** Every Core IR term has a valid location
3. **Synthetic Clarity:** Compiler-generated code clearly labeled
4. **Meta Traceability:** Can always answer "where did ?123 come from?"
5. **Constraint Clarity:** Can always answer "why are we unifying X and Y?"
6. **Error Quality:** Users understand what went wrong and where
7. **LSP Compatibility:** Locations work in editor hover/go-to-definition
8. **CIRCT Readiness:** Locations ready for MLIR emission

---

## Open Questions

1. **Should `Value` carry locations?** Probably not (values are semantic), but needs decision
2. **Granularity of synthetic labels?** How detailed should `Location::synthetic("...")` labels be?
3. **Constraint history depth?** How much constraint solving history to preserve?
4. **Performance impact?** Location interning should be cheap, but needs profiling
5. **VFS integration?** How do locations interact with unsaved LSP buffers?

---

## Dependencies

- **VFS (ADR-008):** Must be implemented first for `SourceFile` → `LineInfo` query
- **Salsa:** Location interning requires salsa database
- **Error reporting crate:** Consider `codespan-reporting` or `ariadne` for nice output

