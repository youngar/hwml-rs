# Diagnostic Framework - Quick Start Guide

**Date:** 2026-05-08  
**For:** Developers implementing HWML diagnostics  
**See Also:** `research/diagnostic-framework-design.md`, `research/DIAGNOSTIC-SYSTEM-SUMMARY.md`

---

## TL;DR

**Goal:** Combine Asai's elaboration backtrace with HWML's unique constraint provenance for best-in-class diagnostics.

**Key Insight:** Users need to know both "how did we get here?" (elaboration backtrace) and "why was this constraint created?" (provenance).

---

## What We're Adding

### 1. Elaboration Backtrace (from Asai)

**Before:**
```
error: type mismatch
  expected: Nat
  got:      Bool
```

**After:**
```
error[E001]: type mismatch at src/main.hwml:42:10
  expected: Nat
  got:      Bool

elaboration backtrace:
  0: checking expression against Nat at src/main.hwml:42:10
  1: checking function return type at src/main.hwml:40:5
  2: checking definition 'process' at src/main.hwml:38:1
```

### 2. Error Codes (from Asai)

**Before:** `error: type mismatch`  
**After:** `error[E001]: type mismatch`

**Benefit:** Users can Google "HWML E001" for help.

### 3. Location Inheritance (from Asai)

**Before:** Manual threading
```rust
let location = expr_location(db, expr);
Err(ElabError::NotInScope { 
    name, 
    span: Some(location.clone())  // Verbose!
})
```

**After:** Automatic from context
```rust
Err(elab.error_not_in_scope(name))  // Location inherited!
```

---

## Implementation Pattern

### Step 1: Add DiagnosticContext to Elaborator

```rust
pub struct DiagnosticContext<'db> {
    trace_stack: Vec<DiagnosticFrame<'db>>,
    current_location: Option<SourceRange<'db>>,
}

pub struct DiagnosticFrame<'db> {
    description: String,
    location: Option<SourceRange<'db>>,
}

pub struct Elaborator<'a, 'db> {
    pub kernel: Kernel<'a, 'db>,
    pub diagnostics: DiagnosticContext<'db>,  // NEW!
}
```

### Step 2: RAII Trace Guard

```rust
pub struct TraceGuard<'a, 'db> {
    context: &'a mut DiagnosticContext<'db>,
}

impl<'a, 'db> Drop for TraceGuard<'a, 'db> {
    fn drop(&mut self) {
        self.context.trace_stack.pop();
    }
}

impl<'db> DiagnosticContext<'db> {
    pub fn trace<'a>(
        &'a mut self,
        description: impl Into<String>,
        location: Option<SourceRange<'db>>,
    ) -> TraceGuard<'a, 'db> {
        if let Some(loc) = location.clone() {
            self.current_location = Some(loc.clone());
        }
        self.trace_stack.push(DiagnosticFrame {
            description: description.into(),
            location,
        });
        TraceGuard { context: self }
    }
}
```

### Step 3: Instrument Elaboration

```rust
pub fn check<'db>(
    db: &'db Db,
    elab: &mut Elaborator<'_, 'db>,
    expr: &Expression,
    expected: RcTy<'db>,
) -> Result<RcSyntax<'db>, ElabError<'db>> {
    let loc = expr_location(db, expr);
    let _guard = elab.diagnostics.trace(
        format!("checking expression against {}", display_ty(&expected)),
        Some(loc),
    );
    
    // ... elaboration logic
    // _guard automatically pops on return/error
}
```

### Step 4: Add Error Codes

```rust
impl<'db> ElabError<'db> {
    pub fn code(&self) -> &'static str {
        match self {
            ElabError::TypeMismatch { .. } => "E001",
            ElabError::NotInScope { .. } => "E002",
            ElabError::CannotInfer { .. } => "E003",
            ElabError::UnificationFailure { .. } => "E004",
            ElabError::OccursCheck { .. } => "E005",
            ElabError::UnsolvedMeta { .. } => "E006",
            // ...
        }
    }
}
```

### Step 5: Enhanced Display

```rust
impl<'db> Display for ElabError<'db> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "error[{}]: ", self.code())?;
        // ... primary message ...
        
        if !backtrace.is_empty() {
            writeln!(f, "\nelaboration backtrace:")?;
            for (i, frame) in backtrace.iter().rev().enumerate() {
                writeln!(f, "  {}: {}", i, frame.description)?;
            }
        }
        
        // ... constraint context (existing) ...
    }
}
```

---

## Key Design Principles

### 1. Five Independent Parameters

Every diagnostic should specify independently:
1. **Fatality** - Stop or continue?
2. **Error Code** - "E001" (Google-able)
3. **Severity** - Error / Warning / Info / Hint / Bug
4. **Backtrace** - How did we get here?
5. **Extra Remarks** - Additional notes

### 2. Byte-Level Positions

- ✅ Use byte offsets, not column numbers
- ✅ Convert to line:column lazily for display
- ✅ Works reliably with Unicode
- ✅ Already implemented (ADR-014)

### 3. Location Inheritance

- Store current location in `DiagnosticContext`
- Errors inherit location automatically
- Less verbose, harder to forget

### 4. RAII > Effect Handlers

- Asai uses OCaml algebraic effects
- Rust uses RAII guards (Drop trait)
- Same ergonomics, different mechanism

---

## Implementation Checklist

- [ ] Create `DiagnosticContext` type
- [ ] Add `TraceGuard` RAII utility
- [ ] Add `diagnostics` field to `Elaborator`
- [ ] Add `code()` method to all error types
- [ ] Wrap `check()` with trace guard
- [ ] Wrap `synth()` with trace guard
- [ ] Add error helper methods to `Elaborator`
- [ ] Update `Display` to show backtrace
- [ ] Create `docs/error-codes.md`
- [ ] Add LSP diagnostic conversion

**Estimated Time:** 2-3 weeks

---

## Further Reading

- **Design:** `research/diagnostic-framework-design.md` - Full design document
- **Summary:** `research/DIAGNOSTIC-SYSTEM-SUMMARY.md` - Research overview
- **Asai Review:** `research/asai-detailed-review.md` - Deep dive into Asai
- **Comparison:** `research/asai-vs-hwml-comparison.md` - Gap analysis
- **Asai Source:** `external/asai/` - Original library

