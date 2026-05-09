# Cross-File Source Tracking: Visual Guide

**Date:** 2026-05-08

---

## The System Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                     Source Files                             │
├─────────────────────────────────────────────────────────────┤
│  lib.hwml              │  main.hwml                          │
│  def f (x:Nat):Bool    │  open MyLib                         │
│                        │  def test:Bool = f true             │
└─────────────────────────────────────────────────────────────┘
           │                          │
           │                          │
           ▼                          ▼
┌─────────────────────────────────────────────────────────────┐
│              DeclInfo (per declaration)                      │
├─────────────────────────────────────────────────────────────┤
│  DeclInfo {                │  DeclInfo {                     │
│    qname: MyLib.f          │    qname: test                  │
│    stmt: Def(...)          │    stmt: Def(...)               │
│    resolver: <MyLib ctx>   │    resolver: <with MyLib open>  │
│    source: Source(lib)  ✅ │    source: Source(main)      ✅ │
│  }                         │  }                              │
└─────────────────────────────────────────────────────────────┘
           │                          │
           │                          │
           ▼                          ▼
┌─────────────────────────────────────────────────────────────┐
│          Elaboration (per declaration)                       │
├─────────────────────────────────────────────────────────────┤
│  Elaborator {             │  Elaborator {                    │
│    context: {             │    context: {                    │
│      current_source:      │      current_source:             │
│        Source(lib) ✅     │        Source(main) ✅          │
│      trace_stack: [       │      trace_stack: [              │
│        ElabFrame {        │        ElabFrame {               │
│          location:        │          location:               │
│            Source(lib)    │            Source(main):20..24   │
│        }                  │        }                         │
│      ]                    │      ]                           │
│    }                      │    }                             │
│  }                        │  }                               │
└─────────────────────────────────────────────────────────────┘
                                     │
                                     ▼
                          ┌──────────────────────┐
                          │   Error Occurs!      │
                          │   f expects Nat,     │
                          │   got Bool           │
                          └──────────────────────┘
                                     │
                                     ▼
┌─────────────────────────────────────────────────────────────┐
│                  Constraint Created                          │
├─────────────────────────────────────────────────────────────┤
│  ConstraintOrigin::FunctionApplication {                     │
│    function_span: SourceRange {                             │
│      source: Source(main),  ← where 'f' is called           │
│      range: 18..19                                           │
│    },                                                        │
│    argument_span: SourceRange {                             │
│      source: Source(main),  ← where 'true' is passed        │
│      range: 20..24                                           │
│    }                                                         │
│  }                                                           │
└─────────────────────────────────────────────────────────────┘
                                     │
                                     ▼
┌─────────────────────────────────────────────────────────────┐
│                    Error Display                             │
├─────────────────────────────────────────────────────────────┤
│  error[E001]: type mismatch at main.hwml:20..24             │
│    expected: Nat                                             │
│    got:      Bool                                            │
│                                                              │
│  elaboration backtrace:                                      │
│    0: checking argument at main.hwml:20..24                  │
│    1: checking application at main.hwml:18..25               │
│    2: checking definition 'test' at main.hwml:15..30         │
│                                                              │
│  constraint context:                                         │
│    origin: function application                              │
│      function at main.hwml:18..19                            │
│      argument at main.hwml:20..24                            │
└─────────────────────────────────────────────────────────────┘
```

---

## Key: What Each Layer Tracks

### Layer 1: Source Files → DeclInfo

**Purpose:** Associate each declaration with its source file

```
DeclInfo.source = Source<'db>  (interned file ID)
```

**Why:** When we elaborate a declaration later, we know which file it came from.

---

### Layer 2: DeclInfo → Elaborator

**Purpose:** Set up elaboration context for the declaration's file

```
Elaborator.context.current_source = decl_info.source
```

**Why:** Errors during elaboration point to the correct file.

---

### Layer 3: Elaboration → Trace Stack

**Purpose:** Track the call stack of elaboration operations

```
ElabFrame {
  location: SourceRange {
    source: current_source,  ← from context
    range: expr_byte_range(expr)
  }
}
```

**Why:** Backtrace shows where we were when the error occurred.

---

### Layer 4: Elaboration → Constraints

**Purpose:** Track where constraints came from (possibly multiple files)

```
ConstraintOrigin::FunctionApplication {
  function_span: SourceRange { source: main.hwml, ... },
  argument_span: SourceRange { source: main.hwml, ... },
}
```

**Why:** Show both the call site and argument site in errors.

---

## Cross-File Example Breakdown

### Setup

```
lib.hwml:
  1: namespace MyLib
  2: def reverse (A:Type) (x:A) (y:A) : (A,A) = (y,x)

main.hwml:
  1: open MyLib
  2: def test : (Nat,Nat) = reverse Bool 1 2
     Range:                 ^^^^^^^^^^^^^^^^^
     Bytes:                 22..43
```

### Step-by-Step

**1. Gather Declarations**

```
programs = [
  (PathBuf("lib.hwml"), Program([...])),
  (PathBuf("main.hwml"), Program([...])),
]

all_decls = [
  DeclInfo {
    qname: MyLib.reverse,
    source: Source(lib.hwml),  ← created from PathBuf
  },
  DeclInfo {
    qname: test,
    source: Source(main.hwml), ← created from PathBuf
  },
]
```

**2. Elaborate 'test'**

```
let decl_info = all_decls[1];  // test
let elab = Elaborator::new(..., decl_info.source);

elab.context.current_source == Source(main.hwml) ✅
```

**3. Trace Guard Created**

```
let _guard = elab.context.trace(
  "checking definition",
  0..50,  // byte range of whole def
  CheckingDefinition { name: "test" },
);

// Adds to stack:
ElabFrame {
  location: SourceRange {
    source: Source(main.hwml), ← from current_source
    range: 0..50,
  },
  ...
}
```

**4. Synthesize 'reverse Bool 1 2'**

```
let _guard = elab.context.trace(
  "synthesizing application",
  22..43,  // byte range of expression
  SynthesizingType,
);

// Adds to stack:
ElabFrame {
  location: SourceRange {
    source: Source(main.hwml), ← from current_source
    range: 22..43,
  },
  ...
}
```

**5. Type Mismatch Detected**

```
// Expected: (Nat, Nat)
// Got:      (Bool, Bool)

ElabError::TypeMismatch {
  span: elab.context.current_location(),
  // Returns: SourceRange {
  //   source: Source(main.hwml), ✅
  //   range: 22..43,
  // }
  
  elab_backtrace: elab.context.snapshot(),
  // Returns: [
  //   ElabFrame { location: main.hwml:22..43, ... },
  //   ElabFrame { location: main.hwml:0..50, ... },
  // ] ✅
}
```

**6. Error Display**

```
error[E001]: type mismatch at main.hwml:22..43
  expected: (Nat, Nat)
  got:      (Bool, Bool)

elaboration backtrace:
  0: synthesizing application at main.hwml:22..43
  1: checking definition 'test' at main.hwml:0..50
```

---

## What About Definition Sites?

**Q:** Can we show "reverse defined at lib.hwml:2"?

**A:** Not yet! That requires storing definition locations in GlobalEnv.

**Current:**
```rust
pub struct ConstantInfo<'db> {
    pub ty: RcSyntax<'db>,
    pub val: RcSyntax<'db>,
    // ❌ No definition_site!
}
```

**Phase 5:**
```rust
pub struct ConstantInfo<'db> {
    pub ty: RcSyntax<'db>,
    pub val: RcSyntax<'db>,
    pub definition_site: Option<SourceRange<'db>>,  // NEW!
}
```

Then we can show:
```
error: type mismatch
  --> main.hwml:22..43
   |
   | def test : (Nat,Nat) = reverse Bool 1 2
   |                        ^^^^^^^^^^^^^^^^
   |
  note: 'reverse' defined here
   --> lib.hwml:2:5
   |
   | def reverse (A:Type) (x:A) (y:A) : (A,A) = ...
   |     ^^^^^^^
```

**But that's Phase 5!** For now, we correctly show WHERE the error occurred.

---

## Summary

**✅ Each layer correctly tracks file information:**

1. **DeclInfo:** Knows which file the declaration came from
2. **ElabContext:** Tracks which file is currently being elaborated
3. **ElabFrame:** Each frame has its own location (can span files in backtrace)
4. **Constraint:** Each span has its own source (can reference multiple files)
5. **Error:** Shows the current file where elaboration failed

**🎯 The design is sound for cross-file constraints!**
