# Cross-File Source Tracking: Deep Analysis Summary

**Date:** 2026-05-08  
**Question:** Does context-based source tracking work for cross-file constraints?  
**Answer:** YES, but we need to add source threading through DeclInfo

---

## TL;DR

**✅ The architecture is fundamentally SOUND**

**❌ Implementation is INCOMPLETE** - using synthetic sources everywhere

**🔧 Fix Required:** Add `source: Source<'db>` to `DeclInfo` (2-3 hours)

---

## Key Findings

### 1. Constraints Already Support Cross-File ✅

From `crates/hwml-elab/src/constraint.rs`:

```rust
pub enum ConstraintOrigin<'db> {
    FunctionApplication {
        function_span: SourceRange<'db>,   // Can be lib.hwml
        argument_span: SourceRange<'db>,   // Can be main.hwml
        param_index: usize,
    },
}
```

Each `SourceRange<'db>` includes its own `Source<'db>`, so a **single constraint can reference multiple files**.

**Verdict:** ✅ No architectural issue here!

---

### 2. ElabContext Correctly Tracks Current File ✅

```rust
pub struct ElabContext<'db> {
    current_source: Source<'db>,           // Which file we're elaborating
    current_byte_range: Option<Range<usize>>,
    trace_stack: Vec<ElabFrame<'db>>,     // Each frame has its own location
}
```

**Key Insight:** `current_source` is just a **convenience** for the current file being elaborated.

Each `ElabFrame` in the backtrace has its **own** `SourceRange<'db>` which can point to **any** file!

**Verdict:** ✅ Design is correct!

---

### 3. The Real Problem: DeclInfo Doesn't Track Source ❌

**Current structure (crates/hwml-elab/src/scc.rs:230):**

```rust
pub struct DeclInfo<'db> {
    pub index: usize,
    pub qualified_name: QualifiedName<'db>,
    pub stmt: Statement,
    pub resolver: Resolver<'db>,  // ✅ Tracks file-local resolver
    // ❌ NO SOURCE!
}
```

**Where this breaks:**

1. **File gathering** (`program.rs:726`):
   ```rust
   for (source_path, program) in programs {
       // source_path is HERE but not captured!
       gather_declarations(..., &mut all_decls);
   }
   ```

2. **Declaration elaboration** (`scc_elab.rs:436`):
   ```rust
   let source = synthetic_source(db, "constant_body");  // ❌ WRONG!
   let mut elab = Elaborator::new(..., source);
   ```

**Result:** All errors show "synthetic" instead of real file names.

**Verdict:** ❌ Critical gap! Easy fix though.

---

## The Fix

### Required Changes

**1. Add source to DeclInfo:**
```rust
pub struct DeclInfo<'db> {
    // ... existing fields
    pub source: Source<'db>,  // NEW!
}
```

**2. Thread source through gather_declarations:**
```rust
fn gather_declarations<'db, Db>(
    // ... existing params
    source: Source<'db>,  // NEW parameter
    out: &mut Vec<DeclInfo<'db>>,
) {
    // ... create DeclInfo with source ...
}
```

**3. Create Source at entry point:**
```rust
for (source_path, program) in programs {
    let source = source_from_path(db, source_path, library_name);
    gather_declarations(..., source, &mut all_decls);
}
```

**4. Use DeclInfo.source in elaboration:**
```rust
let mut elab = Elaborator::new(..., decl_info.source);  // ✅
```

**Estimated effort:** 2-3 hours

---

## Test Cases

### Case 1: Single File Error

**Before:**
```
error: type mismatch at synthetic:10..15
```

**After:**
```
error: type mismatch at main.hwml:10..15
```

---

### Case 2: Cross-File Constraint

**lib.hwml:**
```rust
def f (x : Nat) : Bool = x = 0
```

**main.hwml:**
```rust
def test : Bool = f true
```

**Constraint:**
```rust
ConstraintOrigin::FunctionApplication {
    function_span: SourceRange { source: main.hwml, range: 18..19 },  // `f`
    argument_span: SourceRange { source: main.hwml, range: 20..24 },  // `true`
}
```

**Error:**
```
error: type mismatch at main.hwml:20..24
  expected: Nat (from parameter of 'f')
  got:      Bool
  
  help: function 'f' expects Nat at parameter 0
```

**Note:** The function DEFINITION location (lib.hwml:1) is NOT in the constraint.  
That's correct! The error is about the APPLICATION, not the definition.

To show "defined at lib.hwml:1" → need to store definition sites in GlobalEnv (Phase 5).

---

### Case 3: Backtrace Across Files

**lib.hwml:**
```rust
def apply (A B : Type) (f : A -> B) (x : A) : B = f x
```

**main.hwml:**
```rust
def not (x : Bool) : Bool = ...
def test : Nat = apply Bool Nat not true
```

**Error with backtrace:**
```
error[E001]: type mismatch at main.hwml:50..53
  expected: Bool -> Nat
  got:      Bool -> Bool
  
elaboration backtrace:
  0: checking argument at main.hwml:50..53      (not)
  1: checking application at main.hwml:38..60   (apply ...)
  2: checking definition 'test' at main.hwml:35..65
```

**Note:** All backtrace locations point to main.hwml (where the error occurred).  
The definition of `apply` in lib.hwml is NOT in the backtrace (correct!).

---

## Architectural Principles

### Principle 1: Elaboration Context = Current File

`ElabContext.current_source` tracks **which file is being elaborated right now**.

Errors during elaboration of `main.hwml` should point to `main.hwml`.

**✅ This is correct design!**

---

### Principle 2: Constraints Can Span Files

A single constraint can reference:
- Function call in `main.hwml`
- Function definition type from `lib.hwml` (via GlobalEnv)
- Both locations preserved

**✅ Already supported!**

---

### Principle 3: Definition Sites ≠ Elaboration Sites

**Elaboration backtrace** shows the call stack:
- "We were checking main.hwml:10"
- "Which called checking main.hwml:5"
- "Which was the top-level definition"

**Definition site** shows where something was defined:
- "Function 'f' defined at lib.hwml:42"

These are **orthogonal** concerns!

- **Phase 4:** Elaboration backtrace ✅
- **Phase 5:** Definition sites (requires GlobalEnv changes)

---

## FAQ

**Q: What if a constraint involves types from different files?**

A: Each `SourceRange` in the constraint carries its own `Source<'db>`.  
A single `ConstraintOrigin::FunctionApplication` can have:
- `function_span.source = lib.hwml`
- `argument_span.source = main.hwml`

**Both are preserved correctly!**

---

**Q: What if we're elaborating lib.hwml and reference main.hwml?**

A: During elaboration of `lib.hwml`:
- `current_source = lib.hwml`
- Errors point to `lib.hwml`

If `lib.hwml` somehow referenced `main.hwml` (circular import), that would be a semantic error caught earlier.

In practice, the elaboration order (SCCs) ensures we elaborate in dependency order.

---

**Q: What about metavariable origins?**

A: `MetaOrigin` already includes `span: Option<SourceRange<'db>>`:

```rust
pub enum MetaOrigin<'db> {
    Underscore { span: SourceRange<'db> },  // ✅ Has source!
    // ...
}
```

Each meta knows which file it came from. No issue here!

---

## Conclusion

### The Verdict: ✅ SOUND ARCHITECTURE

**Does context-based source tracking work for cross-file constraints?**

**YES!** The design is fundamentally correct:

1. ✅ Constraints support cross-file (multiple SourceRanges)
2. ✅ ElabContext tracks current file (correct for errors)
3. ✅ Each backtrace frame has its own location (can span files)
4. ✅ Metavariables track their source
5. ✅ SourceRange is properly interned (cheap to copy)

**What's missing?**

We're using synthetic sources instead of real file paths.

**Fix:** Add `source: Source<'db>` to `DeclInfo` (2-3 hours).

---

### Next Steps

**Immediate (Phase 4.0 completion):**
1. Add `source` field to `DeclInfo`
2. Thread through `gather_declarations`
3. Use at elaboration sites
4. Remove synthetic sources

**Future (Phase 5):**
- Store definition sites in GlobalEnv
- Multi-span diagnostics with Ariadne
- "defined at lib.hwml:10" in error messages

---

**The architecture passes the cross-file test!** 🎉✅
