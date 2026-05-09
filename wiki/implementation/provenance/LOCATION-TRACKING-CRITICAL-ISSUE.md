# CRITICAL ISSUE: Location Tracking Across Files

**Date:** 2026-05-08  
**Severity:** 🔴 **HIGH** - Affects Phase 4 diagnostic quality  
**Status:** Design flaw identified - requires fix before Phase 4

---

## Problem Statement

**User Question:**
> "What is our plan for mapping locations back to the original file location? We are elaborating across files but we are only tracking spans?"

**The Issue:**
Our current `SourceRange<'db>` system **does** track which file a span comes from via `Source<'db>`, **BUT** we're creating spans incorrectly during elaboration. Most elaboration code creates **synthetic** sources instead of preserving the real file source.

---

## Current System Analysis

### ✅ What We Have (Infrastructure is Good!)

```rust
// In crates/hwml-core/src/source_range.rs

#[salsa::interned]
pub struct SourceFileId {
    pub library_name: Word<'db>,      // "my-hardware"
    pub canonical_path: Word<'db>,    // "/workspace/my-hardware/src/adder.hwml"
}

pub enum SourceInfo<'db> {
    File(SourceFileId<'db>),  // ✅ Real file with full path
    Synthetic(Word<'db>),      // For compiler-generated code
}

#[salsa::interned]
pub struct Source {
    pub info: SourceInfo<'db>,
}

pub struct SourceRange<'db> {
    pub source: Source<'db>,   // ✅ Includes file information!
    pub range: Range<usize>,   // Byte offsets
}
```

**The infrastructure is correct!** `SourceRange` CAN represent locations across multiple files.

---

### ❌ What's Wrong (Usage is Broken!)

**Problem:** During elaboration, we're creating **synthetic** sources instead of preserving real file sources.

**Evidence from codebase:**

#### Example 1: `elab/expr.rs` Line 126-131
```rust
Expression::Universe(u) => {
    let word = Word::new(db, "universe");  // ❌ Creating synthetic word
    let source = Source::new(db, SourceInfo::Synthetic(word));  // ❌ SYNTHETIC!
    let span = SourceRange::new(source, u.loc.clone());
    // ^^^ This span has NO file information!
}
```

**Should be:**
```rust
Expression::Universe(u) => {
    let span = expr_location(db, expr);  // ✅ Preserves real file source
    elab.kernel.synth_universe(db, None, Some(span))
}
```

#### Example 2: `elab/expr.rs` Line 204-207
```rust
let word = Word::new(db, name);
let source = Source::new(db, SourceInfo::Synthetic(word));  // ❌ SYNTHETIC!
let span = SourceRange::new(source, id.loc.clone());
```

#### Example 3: Dot field access (Line 237-241)
```rust
let create_span = |range: &std::ops::Range<usize>, desc: &str| {
    let word = Word::new(db, desc);
    let source = Source::new(db, SourceInfo::Synthetic(word));  // ❌ SYNTHETIC!
    SourceRange::new(source, range.clone())
};
```

**The pattern is everywhere:** We're creating synthetic sources instead of getting the real source from the surface syntax.

---

## Root Cause

### Missing: Surface → Core Source Propagation

**The Problem Chain:**

1. **Surface Syntax has locations** (`hwml_surface::Expression` has `loc: Range<usize>`)
2. **But NO SOURCE** - just byte ranges
3. **Parser doesn't attach Source** to AST nodes
4. **Elaborator creates synthetic sources** because it doesn't know the real file

**What's missing:**
```rust
// Surface syntax (current):
pub struct Id {
    pub value: Box<str>,
    pub loc: Range<usize>,  // ❌ No source file info!
}

// Surface syntax (needed):
pub struct Id<'db> {
    pub value: Box<str>,
    pub loc: Range<usize>,
    pub source: Source<'db>,  // ✅ Which file is this from?
}
```

---

## Impact on Phase 4

### Current State: Broken Multi-File Diagnostics

**Scenario:** User imports function from `lib.hwml`, uses it in `main.hwml`

```
// lib.hwml
def add(x: Nat, y: Nat): Nat = x + y

// main.hwml
def test = add(true, 42)  // Error: expected Nat, got Bool
```

**Current error output:**
```
error[E001]: type mismatch at 11..15
  expected: Nat
  got:      Bool

elaboration backtrace:
  0: checking expression against Nat at 11..15
  1: checking function application at 8..20
  2: checking definition 'test' at 1..100

Source: "synthetic" ❌ NO FILE NAME!
```

**What we need:**
```
error[E001]: type mismatch
  --> main.hwml:2:15
   |
 2 | def test = add(true, 42)
   |                ^^^^ expected Nat, got Bool
   |
note: function defined here
  --> lib.hwml:1:1
   |
 1 | def add(x: Nat, y: Nat): Nat = x + y
   | ^^^ function 'add' expects first parameter of type Nat
```

---

## Solutions

### Solution 1: Thread Source Through Surface Syntax (Recommended)

**Effort:** Medium (2-3 days)  
**Impact:** Fixes the root cause  
**Quality:** Best - preserves exact file locations

**Implementation:**

#### Step 1: Update Surface Syntax
```rust
// In hwml-surface/src/ast.rs (or equivalent)

use hwml_core::Source;

pub struct Id<'db> {
    pub value: Box<str>,
    pub loc: Range<usize>,
    pub source: Source<'db>,  // NEW!
}

// Same for all other AST nodes
```

#### Step 2: Update Parser to Attach Source
```rust
// During parsing
pub fn parse_expression<'db>(
    db: &'db dyn salsa::Database,
    source: Source<'db>,  // Passed from parse_file
    input: &str,
) -> Expression<'db> {
    // Parser actions attach source to every node
    Id {
        value: text.into(),
        loc: start..end,
        source: source.clone(),  // ✅ Real file source!
    }
}
```

#### Step 3: Update expr_location to Use Real Source
```rust
// In elab/expr.rs
fn expr_location<'db>(db: &'db dyn salsa::Database, expr: &Expression<'db>) -> SourceRange<'db> {
    match expr {
        Expression::Id(id) => SourceRange::new(id.source, id.loc.clone()),  // ✅ Real source!
        Expression::Universe(u) => SourceRange::new(u.source, u.loc.clone()),
        // ... all other cases use real source
    }
}
```

**Benefits:**
- ✅ Correct file tracking
- ✅ Works across imports/modules
- ✅ No guessing or heuristics
- ✅ Diagnostic tools get real file paths

**Drawbacks:**
- Requires parser changes
- Adds `source` field to all AST nodes (~10% code churn)

---

### Solution 2: Context-Based Source Tracking (Quick Fix)

**Effort:** Low (1 day)  
**Impact:** Partial fix  
**Quality:** Good for single-file, hacky for multi-file

**Implementation:**

Add `current_source` to Elaborator:

```rust
pub struct Elaborator<'a, 'db> {
    pub kernel: Kernel<'a, 'db>,
    pub context: ElabContext<'db>,
    pub current_source: Source<'db>,  // NEW!
}

impl<'db> ElabContext<'db> {
    pub fn current_location_with_source(
        &self,
        source: Source<'db>,
    ) -> Option<SourceRange<'db>> {
        self.current_location.as_ref().map(|range| {
            SourceRange::new(source, range.range.clone())
        })
    }
}
```

**Usage:**
```rust
pub fn synth<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
) -> Result<...> {
    // Store source at start of file elaboration
    let _guard = elab.context.trace(
        "synthesizing type",
        SourceRange::new(elab.current_source, expr.loc()),  // ✅ Use context source
        ElabFrameKind::SynthesizingType,
    );
    // ...
}
```

**Benefits:**
- ✅ Quick to implement
- ✅ No parser changes
- ✅ Works for most cases

**Drawbacks:**
- ❌ Loses precision when crossing file boundaries
- ❌ Requires manual source management
- ❌ Error-prone (easy to forget to update `current_source`)

---

### Solution 3: Post-Processing Source Fixup (Hack)

**Effort:** Low (hours)  
**Impact:** Minimal  
**Quality:** Poor - band-aid solution

Don't do this. Just documenting for completeness.

---

## Recommendation

### Phase 4.0: Fix Source Tracking (BEFORE other Phase 4 work)

**Timeline:**
- **Phase 4.0 (NEW):** Fix source tracking (2-3 days)
- **Phase 4.1:** Infrastructure (1 day) 
- **Phase 4.2-4.5:** Implementation as planned (4-6 days)

**Total:** 7-10 days instead of 5-7 days

**Rationale:**
- Without correct sources, Phase 4 backtraces will show "synthetic" instead of file names
- This defeats the entire purpose of better diagnostics
- Fixing it later will require re-testing everything
- Better to fix the foundation first

---

## Action Items

### Immediate (Before Starting Phase 4)

- [ ] **Decision:** Choose Solution 1 (recommended) or Solution 2 (quick)
- [ ] **If Solution 1:** Design Surface Syntax Changes
  - [ ] Add `source: Source<'db>` to all AST node types
  - [ ] Update parser to thread source through
  - [ ] Update all pattern matches (compiler helps)
  
- [ ] **If Solution 2:** Add current_source to Elaborator
  - [ ] Update `Elaborator` struct
  - [ ] Add source tracking to file elaboration entry points
  - [ ] Update `expr_location` to use context source

### Phase 4 Implementation

- [ ] Update `expr_location()` to preserve real sources
- [ ] Remove all `Source::new(db, SourceInfo::Synthetic(...))` calls
- [ ] Verify error messages show real file paths
- [ ] Test multi-file error reporting

---

## Test Cases Needed

### Single-File Errors (Should Already Work)
```hwml
// main.hwml
def foo: Nat = true  // Error at main.hwml:1:16
```

### Cross-File Errors (Currently Broken)
```hwml
// lib.hwml
def helper(x: Nat): Nat = x

// main.hwml  
import lib
def test = lib.helper(true)  // Error: arg from main.hwml, function from lib.hwml
```

Expected output:
```
error[E001]: type mismatch
  --> main.hwml:2:22
   |
 2 | def test = lib.helper(true)
   |                       ^^^^ expected Nat, got Bool
   |
note: function 'helper' defined here
  --> lib.hwml:1:1
   |
 1 | def helper(x: Nat): Nat = x
   |            ^^^^^^ parameter expects Nat
```

---

## References

- **Current Source System:** `crates/hwml-core/src/source_range.rs`
- **Problem Sites:** `crates/hwml-elab/src/elab/expr.rs` (Lines 126, 204, 237)
- **Related:** Ariadne multi-file diagnostics (Phase 5)
