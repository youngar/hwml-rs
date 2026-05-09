# Phase 4.0: Concrete Cross-File Example

**Date:** 2026-05-08  
**Status:** Demonstrating the problem and solution

---

## The Scenario

**Project structure:**
```
my-lib/
  src/
    lib.hwml     - defines `reverse`
    main.hwml    - uses `reverse` incorrectly
```

**lib.hwml:**
```rust
namespace MyLib

def reverse (A : Type) (x : A) (y : A) : (A, A) = (y, x)
```

**main.hwml:**
```rust
open MyLib

def test : (Nat, Nat) = reverse Bool 1 2
                        ^^^^^^^ ERROR: Bool vs Nat mismatch
```

---

## Current Code Flow

### 1. File Gathering (program.rs:726)

```rust
for (source_path, program) in programs {
    //  ^^^^^^^^^^^ 
    //  source_path = PathBuf("my-lib/src/lib.hwml")
    
    let mut file_resolver = Resolver::new();
    
    // ... process opens ...
    
    gather_declarations(
        db,
        &program.statements,
        None,
        &file_resolver,
        &mut all_decls,  // Accumulates DeclInfo
    );
}
```

**Problem:** `source_path` is available HERE but NOT passed to `gather_declarations`!

### 2. DeclInfo Creation (current - BROKEN)

```rust
// Inside gather_declarations():
out.push(DeclInfo {
    index: out.len(),
    qualified_name: MyLib.reverse,
    stmt: Statement::Def(...),  // The AST for `reverse`
    resolver: file_resolver.clone(),
    // ❌ NO SOURCE! Lost the source_path!
});
```

### 3. Elaboration (scc_elab.rs:369)

```rust
for (stmt, header) in scc {
    let decl_info = &decls[stmt.index];
    
    let source = synthetic_source(db, "inductive_body");
    //           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    //           ❌ Using synthetic! Should use decl_info.source
    
    let mut elab = Elaborator::new(..., source);
    
    // Elaborate the body of `reverse`
    // Errors will show "synthetic" instead of "lib.hwml"!
}
```

### 4. Error in main.hwml

When elaborating `main.hwml`:

```rust
// In elab_library_with_sccs, second iteration:
for (source_path, program) in programs {
    // source_path = "my-lib/src/main.hwml"
    
    gather_declarations(...);  // Gets `test` declaration
}

// Later, in elaborate_bodies:
// Elaborating `test` from main.hwml
let source = synthetic_source(db, "constant_body");
//           ❌ Should be Source(main.hwml)!

let mut elab = Elaborator::new(..., source);

// Check: reverse Bool 1 2
// Error occurs: Bool ≠ Nat
ElabError::TypeMismatch {
    span: elab.context.current_location(),
    // Returns: SourceRange { 
    //   source: Source(Synthetic("constant_body")),  ❌ WRONG!
    //   range: 32..46 
    // }
}
```

**Result:** Error shows `"synthetic:32..46"` instead of `"main.hwml:32..46"` ❌

---

## The Fix

### Step 1: Update DeclInfo

**File:** `crates/hwml-elab/src/scc.rs`

```rust
use hwml_core::Source;

#[derive(Debug, Clone)]
pub struct DeclInfo<'db> {
    pub index: usize,
    pub qualified_name: QualifiedName<'db>,
    pub stmt: Statement,
    pub resolver: crate::resolver::Resolver<'db>,
    pub source: Source<'db>,  // NEW!
}
```

### Step 2: Update gather_declarations

**File:** `crates/hwml-elab/src/program.rs`

```rust
fn gather_declarations<'db, Db>(
    db: &'db Db,
    statements: &[Statement],
    current_namespace: Option<QualifiedName<'db>>,
    resolver: &Resolver<'db>,
    source: Source<'db>,  // NEW parameter
    out: &mut Vec<crate::scc::DeclInfo<'db>>,
) where
    Db: salsa::Database,
{
    for stmt in statements {
        match stmt {
            Statement::Def(def) => {
                // ... get qualified name ...
                
                out.push(crate::scc::DeclInfo {
                    index: out.len(),
                    qualified_name: qname,
                    stmt: stmt.clone(),
                    resolver: resolver.clone(),
                    source,  // ✅ Capture it!
                });
            }
            
            Statement::Namespace(ns) => {
                // ... qualify namespace ...
                let ns_resolver = resolver.push_namespace(db, &path);
                
                gather_declarations(
                    db,
                    &ns.statements,
                    Some(ns_qname),
                    &ns_resolver,
                    source,  // ✅ Propagate through recursion
                    out,
                );
            }
            
            // ... other cases
        }
    }
}
```

### Step 3: Create Source at Entry Point

**File:** `crates/hwml-elab/src/program.rs`

```rust
pub fn elab_library_with_sccs<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    programs: &[(std::path::PathBuf, &Program)],
    global_stub_table: &StubTable<'db>,
) -> ElabProgramResult<'db> {
    let mut all_decls: Vec<DeclInfo<'db>> = Vec::new();
    
    for (source_path, program) in programs {
        let mut file_resolver = Resolver::new();
        
        // ✅ Create Source from the PathBuf
        let source = source_from_path(db, source_path, "my-lib");
        
        // Process opens...
        
        gather_declarations(
            db,
            &program.statements,
            None,
            &file_resolver,
            source,  // ✅ Pass the source!
            &mut all_decls,
        );
    }
    
    // ... rest of elaboration
}
```

### Step 4: Use DeclInfo.source in Elaboration

**File:** `crates/hwml-elab/src/scc_elab.rs`

```rust
pub fn elaborate_bodies(...) {
    for decl_info in decls {
        match (stmt, header) {
            (Statement::Def(def), DeclHeader::Constant { .. }) => {
                let mut elab = Elaborator::new(
                    global,
                    ty_ctx.clone(),
                    state,
                    decl_resolver,
                    stub_table,
                    decl_info.source,  // ✅ Use declaration's source!
                );
                
                // Now errors show real file!
            }
        }
    }
}
```

---

## After The Fix

### Error Display

**Before:**
```
error: type mismatch at synthetic:32..46
  expected: (Nat, Nat)
  got:      (Bool, Bool)
```

**After:**
```
error: type mismatch at main.hwml:32..46
  expected: (Nat, Nat)
  got:      (Bool, Bool)
```

### With Backtrace (Phase 4.1+)

```
error[E001]: type mismatch at main.hwml:32..46
  expected: (Nat, Nat)
  got:      (Bool, Bool)

elaboration backtrace:
  0: checking expression at main.hwml:32..46
  1: checking definition 'test' at main.hwml:20..50
  2: elaborating file 'main.hwml' at main.hwml:0..100
```

---

## Constraint Example (Cross-File)

**Scenario:** Constraint involves both files

**lib.hwml:**
```rust
def f (x : Nat) : Bool = x = 0
```

**main.hwml:**
```rust
def test : Nat = f true
```

**Constraint Created:**
```rust
ConstraintOrigin::FunctionApplication {
    function_span: SourceRange {
        source: Source(main.hwml),  // Where `f` is referenced
        range: 17..18,
    },
    argument_span: SourceRange {
        source: Source(main.hwml),  // Where `true` is passed
        range: 19..23,
    },
    param_index: 0,
}
```

**Note:** The function DEFINITION in `lib.hwml` is not in the constraint!  
That's because the constraint is about the APPLICATION site, not the definition site.

**To show definition site:** Need to store in GlobalEnv (Phase 5).

---

## Summary

**Q:** Does this work for cross-file constraints?

**A:** YES, after we add `source` to `DeclInfo`!

**The architecture is sound:**
- ✅ Constraints already support cross-file (multiple SourceRanges)
- ✅ Each SourceRange has its own Source
- ✅ ElabContext tracks the current file being elaborated
- ✅ Errors show WHERE the problem occurred (correct file)

**What's missing:**
- ❌ DeclInfo doesn't track source (easy fix!)
- ❌ We're using synthetic sources everywhere (easy fix!)

**Estimated fix time:** 2-3 hours to add source threading.

**Then:** All errors will show real file names! 🎉
