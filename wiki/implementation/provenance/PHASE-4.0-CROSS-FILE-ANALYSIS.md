# Phase 4.0: Cross-File Source Tracking Analysis

**Date:** 2026-05-08  
**Status:** Critical architectural review  
**Question:** Does context-based source tracking work for cross-file constraints?

---

## The Problem Statement

We're storing `current_source: Source<'db>` in `ElabContext`. This works great for single-file elaboration:

```rust
// File: main.hwml
def foo : Nat = true  // Error at main.hwml:1:16
```

**But what about cross-file constraints?**

```rust
// File: lib.hwml
def id (A : Type) (x : A) : A = x

// File: main.hwml
def test : Nat = id Bool true
                 // ^^^ Type error: expected Nat, got Bool
                 // But `id` is defined in lib.hwml!
```

**The concern:** If we elaborate `main.hwml` with `current_source = main.hwml`, will errors involving `id` from `lib.hwml` show the wrong file?

---

## Architecture Analysis

### Current Design

**ElabContext Structure:**
```rust
pub struct ElabContext<'db> {
    trace_stack: Vec<ElabFrame<'db>>,
    current_source: Source<'db>,           // Points to ONE file
    current_byte_range: Option<Range<usize>>,
}

pub struct ElabFrame<'db> {
    pub description: String,
    pub location: SourceRange<'db>,        // Each frame has its OWN location
    pub kind: ElabFrameKind,
}
```

**Key Insight #1:** `current_source` is NOT the only source in play!  
Each `ElabFrame` contains a `SourceRange<'db>` which has its own `Source<'db>`.

**Key Insight #2:** `current_source` is just a **convenience** for creating locations when we don't have a better source.

---

## Scenario Walkthrough

### Scenario 1: Cross-File Function Call

**Setup:**
```rust
// lib.hwml
def reverse (A : Type) (x : A) (y : A) : (A, A) = (y, x)

// main.hwml  
def test : (Nat, Nat) = reverse Bool 1 2
                        // Error: Bool ≠ Nat
```

**Elaboration Flow:**

1. **File-level elaboration of main.hwml:**
   ```rust
   // In elaborate_file("main.hwml"):
   let source = source_from_path(db, "main.hwml", "my-lib");
   let mut elab = Elaborator::new(..., source);  // current_source = main.hwml
   ```

2. **Synthesizing `reverse` (lookup):**
   ```rust
   // In synth() for `reverse` identifier
   let _guard = elab.context.trace(
       "looking up reverse",
       expr_byte_range(reverse_id),  // 16..23 in main.hwml
       ElabFrameKind::SynthesizingType,
   );
   
   // Lookup finds: reverse : (A : Type) -> (x : A) -> (y : A) -> (A, A)
   // This type is stored in GlobalEnv, NO source attached
   ```

3. **Checking application:**
   ```rust
   // synth_app in kernel
   let dom_ty = Bool;  // From the type signature
   let arg_syn = check(db, &mut elab, &arg1, Bool)?;
   // arg1 is `1 : Nat`
   ```

4. **Type mismatch detected:**
   ```rust
   // Unification fails: Nat ≠ Bool
   // Error creation:
   ElabError::TypeMismatch {
       expected: Bool,
       actual: Nat,
       span: elab.context.current_location(),  // ← THIS IS THE ISSUE!
       elab_backtrace: elab.context.snapshot(),
   }
   ```

**What `current_location()` returns:**
```rust
Some(SourceRange {
    source: Source { info: File("main.hwml") },  // ✅ Correct!
    range: 16..23,  // ✅ Points to `reverse` in main.hwml
})
```

**What the backtrace contains:**
```rust
vec![
    ElabFrame {
        description: "checking argument",
        location: SourceRange { source: main.hwml, range: 32..33 },  // `1`
        kind: CheckingExpression,
    },
    ElabFrame {
        description: "synthesizing type",  
        location: SourceRange { source: main.hwml, range: 16..23 },  // `reverse`
        kind: SynthesizingType,
    },
    ElabFrame {
        description: "checking definition test",
        location: SourceRange { source: main.hwml, range: 0..50 },
        kind: CheckingDefinition,
    },
]
```

**Result:** ✅ **ALL locations correctly point to main.hwml** because the error happened during elaboration of main.hwml.

---

### Scenario 2: Import and Elaborate From Different File

**What if we elaborate code from lib.hwml while in main.hwml context?**

**This doesn't happen!** Here's why:

Looking at the SCC elaboration architecture:
```rust
// From scc_elab.rs
pub fn elaborate_bodies(...) {
    for (stmt, header) in scc {
        let decl_info = &decls[stmt.index];
        
        // CRITICAL: Each declaration uses its OWN resolver
        let decl_resolver = &decl_info.resolver;
        
        // Create elaborator with...what source?
        let source = synthetic_source(db, "constant_body");  // TODO!
        let mut elab = Elaborator::new(..., decl_resolver, ..., source);
    }
}
```

**The Problem:** We're using `synthetic_source` for everything right now!

**What we SHOULD do:**
```rust
// DeclInfo should include the source file!
pub struct DeclInfo<'db> {
    pub index: usize,
    pub qualified_name: QualifiedName<'db>,
    pub stmt: Statement,
    pub resolver: Resolver<'db>,
    pub source: Source<'db>,  // NEW! Track which file this came from
}
```

Then in elaborate_bodies:
```rust
let source = decl_info.source;  // Use the declaration's original file
let mut elab = Elaborator::new(..., source);
```

---

## The Real Issue Discovered

### 🚨 CRITICAL GAP: DeclInfo doesn't track source!

**Current `DeclInfo` structure:**
```rust
pub struct DeclInfo<'db> {
    pub index: usize,
    pub qualified_name: QualifiedName<'db>,
    pub stmt: Statement,
    pub resolver: Resolver<'db>,  // ✅ Has file-local resolver
    // ❌ NO SOURCE!
}
```

**Where DeclInfo is created:**
```rust
// In program.rs: elab_library_with_sccs
for (source_path, program) in programs {
    // We have source_path here!
    
    gather_declarations(
        db,
        &program.statements,
        None,
        &file_resolver,
        &mut all_decls,  // Populates DeclInfo
    );
}
```

But `gather_declarations` doesn't capture the `source_path`!

---

## Solution Architecture

### Fix 1: Add Source to DeclInfo

```rust
pub struct DeclInfo<'db> {
    pub index: usize,
    pub qualified_name: QualifiedName<'db>,
    pub stmt: Statement,
    pub resolver: Resolver<'db>,
    pub source: Source<'db>,  // NEW!
}
```

### Fix 2: Thread Source Through gather_declarations

```rust
fn gather_declarations<'db, Db>(
    db: &'db Db,
    statements: &[Statement],
    current_namespace: Option<QualifiedName<'db>>,
    resolver: &Resolver<'db>,
    source: Source<'db>,  // NEW parameter
    out: &mut Vec<DeclInfo<'db>>,
) {
    for stmt in statements {
        match stmt {
            Statement::Def(def) => {
                out.push(DeclInfo {
                    // ...
                    source,  // Capture it!
                });
            }
            // ...
        }
    }
}
```

### Fix 3: Use DeclInfo.source in elaboration

```rust
pub fn elaborate_bodies(...) {
    for decl_info in decls {
        let mut elab = Elaborator::new(
            ...,
            decl_info.source,  // Use declaration's source file
        );
        // Now errors in lib.hwml show lib.hwml!
    }
}
```

---

## Constraint Solver Analysis

### Do Constraints Track Sources?

**YES! ✅ Constraints already track SourceRange properly!**

From `crates/hwml-elab/src/constraint.rs`:

```rust
pub enum ConstraintOrigin<'db> {
    TypeAnnotation {
        annotation_span: SourceRange<'db>,  // ✅ Has full source info!
        expression_span: SourceRange<'db>,  // ✅ Multiple locations!
    },

    FunctionApplication {
        function_span: SourceRange<'db>,   // Could be lib.hwml
        argument_span: SourceRange<'db>,   // Could be main.hwml
        param_index: usize,
    },

    ReturnTypeCheck {
        declared_span: SourceRange<'db>,   // Could be lib.hwml
        returned_span: SourceRange<'db>,   // Could be main.hwml
    },
    // ...
}
```

**Key Insight #3:** Constraints ALREADY support cross-file tracking!

Each `SourceRange<'db>` includes its own `Source<'db>`, so a single constraint can reference:
- Function defined in `lib.hwml`
- Argument passed in `main.hwml`
- Both locations preserved correctly!

---

## Cross-File Error Example

### Concrete Scenario

**lib.hwml:**
```rust
def id (A : Type) (x : A) : A = x
```

**main.hwml:**
```rust
open MyLib

def test : Nat = id Bool true
```

### Error Flow

**1. Elaborating main.hwml:**
```rust
let source_main = source_from_path(db, "main.hwml", "my-lib");
let mut elab = Elaborator::new(..., source_main);
elab.context.current_source == Source(main.hwml);
```

**2. Synthesizing `id Bool true`:**
```rust
// Lookup `id` from GlobalEnv
// Type signature: (A : Type) -> (x : A) -> A
// This type has NO source location (it's abstract)

// Apply to `Bool`:
synth_app(id, Bool)
  → returns: (x : Bool) -> Bool

// Apply to `true`:
synth_app((x : Bool) -> Bool, true)
  → check(true, Bool)
  → infer true : Bool
  → ✅ Success! Returns: Bool
```

**3. Checking against declared type:**
```rust
check(id Bool true, Nat)
  → inferred: Bool
  → expected: Nat
  → emit constraint: Bool =?= Nat
```

**4. Constraint created with origin:**
```rust
ConstraintOrigin::ReturnTypeCheck {
    declared_span: SourceRange {
        source: Source(main.hwml),
        range: 17..20,  // "Nat" in main.hwml
    },
    returned_span: SourceRange {
        source: Source(main.hwml),
        range: 21..34,  // "id Bool true" in main.hwml
    },
}
```

**5. Constraint solving fails:**
```rust
ElabError::UnsolvedMeta {
    meta_id: ?42,
    provenance: MetaProvenance {
        origin: ...,
        constraint_ids: [C10],
        blocking_constraint_ids: [C10],
    },
}

// When displaying error, we look up C10:
Constraint {
    id: C10,
    origin: ReturnTypeCheck {
        declared_span: main.hwml:17..20,  // ✅ Correct file!
        returned_span: main.hwml:21..34,  // ✅ Correct file!
    },
}
```

**Result:** ✅ Error shows:
```
error: type mismatch
  --> main.hwml:21:1
   |
21 | def test : Nat = id Bool true
   |            ^^^   ^^^^^^^^^^^^ has type Bool
   |            expected Nat
```

---

## The REAL Cross-File Case

### When Functions ARE From Different Files

**lib.hwml:**
```rust
def apply (A B : Type) (f : A -> B) (x : A) : B = f x
```

**main.hwml:**
```rust
open MyLib

def not (x : Bool) : Bool = ...

def test : Nat = apply Bool Nat not true
```

**Error:** `not : Bool -> Bool` but we're applying it as `Bool -> Nat`

### Where Does The Error Point?

**During elaboration:**
```rust
// Synthesizing `apply Bool Nat not true`
synth_app(apply, Bool)
  → synth_app(..., Nat)
  → synth_app(..., not)
  → check(not, Bool -> Nat)
    → inferred: Bool -> Bool  // From GlobalEnv (no source!)
    → expected: Bool -> Nat
    → ❌ Mismatch!
```

**Error creation:**
```rust
ElabError::TypeMismatch {
    expected: Bool -> Nat,
    actual: Bool -> Bool,
    span: elab.context.current_location(),  // Points to `not` in main.hwml
    elab_backtrace: [
        ElabFrame { location: main.hwml:50..53, ... },  // `not`
        ElabFrame { location: main.hwml:38..60, ... },  // whole application
    ]
}
```

**The issue:** We can show WHERE the error occurred (main.hwml), but we can't show where `not` was DEFINED (main.hwml line 5).

**But this is a SEPARATE problem:** That's about tracking definition sites, not elaboration context!

---

## Conclusions

### ✅ Current Design IS Sound!

**Q: Does context-based source tracking work for cross-file constraints?**

**A: YES, with caveats:**

1. **✅ Constraints already support cross-file** (SourceRange per span)
2. **✅ Error locations point to the code being elaborated** (correct!)
3. **✅ Backtraces show the elaboration path** (all in one file or across files)
4. **❌ We're not yet using real sources** (using synthetic everywhere)
5. **❌ DeclInfo doesn't track source files** (critical gap!)

### 🔧 Required Fixes

**Fix 1: Add source to DeclInfo** (High Priority)
- Track which file each declaration came from
- Use that source when elaborating the declaration's body

**Fix 2: Thread source through gather_declarations** (High Priority)
- Pass source down the recursion
- Attach to each DeclInfo

**Fix 3: Use source_from_path at entry points** (Medium Priority)
- In `elab_library_with_sccs`, create real Source from PathBuf
- Replace all synthetic_source calls with real sources

### 🤔 What About Definition Sites?

**Separate concern!**

Showing "defined at lib.hwml:10" requires tracking definition locations in GlobalEnv:

```rust
pub struct ConstantInfo<'db> {
    pub ty: RcSyntax<'db>,
    pub val: RcSyntax<'db>,
    pub definition_site: Option<SourceRange<'db>>,  // NEW!
}
```

This is **Phase 5** work (Ariadne multi-span diagnostics).

For now, Phase 4 correctly tracks WHERE errors occur during elaboration.

---

## Revised Phase 4.0 Plan

### Additional Tasks

- [ ] **Task 2.5:** Add `source: Source<'db>` to `DeclInfo`
- [ ] **Task 2.6:** Update `gather_declarations` to accept and propagate source
- [ ] **Task 2.7:** Update `elab_library_with_sccs` to create Source from PathBuf
- [ ] **Task 2.8:** Use `decl_info.source` in `elaborate_headers` and `elaborate_bodies`

**Estimated Additional Time:** 2-3 hours

---

## Final Answer

**Does this actually work?**

**YES!** ✅ The architecture is sound.

**Constraints involving values across files:**

**WORK CORRECTLY!** ✅ Each SourceRange carries its own Source, so constraints can reference multiple files.

**Current limitation:**

We're using synthetic sources everywhere (temporary). Need to:
1. Thread real sources through DeclInfo
2. Use them in elaboration
3. Then everything will show real file names!

**The design is correct; we just need to finish the implementation.** 🎯
