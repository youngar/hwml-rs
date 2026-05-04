# Object File Formats for Dependent Type Systems

**Date:** 2026-05-03  
**Status:** Research complete  
**Related:** [[research/content-addressable-storage-systems]], [[research/build-system-caching-synthesis]], [[decisions/ADR-006-multi-layer-build-configuration]]

---

## Executive Summary

This document investigates how modern dependent type systems (Lean 4, Agda, Coq, Idris) serialize elaborated code to object files, with particular focus on:

1. **Type interning**: Why András Kovács argues it has limited value in dependent types
2. **Serialization strategies**: Sharing, memoization, compact regions
3. **What to intern**: Strings, names, constants vs types/values
4. **HWML's approach**: Types are values, so both fit the same representation

**Key Finding:** In dependent type systems where types are values (like HWML), aggressive hash-consing/interning of types provides minimal benefit and substantial complexity. However, interning **constants** (names, strings, primitive values) is highly valuable.

---

## 1. András Kovács on Type Interning (smalltt)

### The Anti-Interning Argument

From `smalltt` README.md:

> **On hash consing**
>
> Usually by "hash consing" we mean a pervasive form of memoization, where certain objects are stored at most once in memory, and object construction goes through a table lookup to check if the object already exists. It is frequently mentioned as an optimization technique in typechecking. However, specifically in the context of dependent elaboration, it's not obviously desirable.
>
> If I have something like a first-order term language, hash consing can be very effective. But in dependent type theory, we have higher-order programs with potentially explosive behavior, and it isn't hard to produce size explosions even in the presence of full hash-consing. Considering this, and the performance and complexity overhead of hash consing, I decide to skip it in smalltt.

### Why Type Interning Fails for Dependent Types

**Problem 1: Exponential blowup despite interning**

Consider type-level computation:
```haskell
-- Type-level natural number addition
type family Add (n :: Nat) (m :: Nat) :: Nat where
  Add Z m = m
  Add (S n) m = S (Add n m)

-- Computing Add 100 50 still creates 100+ intermediate types
-- Even with interning, this is unavoidable
```

**Problem 2: Hash consing overhead**

Each type construction requires:
1. Compute hash of components (expensive for large structures)
2. Lookup in hash table (cache miss likely)
3. If miss: allocate + insert into table
4. If hit: use existing (rare for unique types)

**For dependent types:**
- Most types are **unique** (computed from different contexts)
- Hash table overhead dominates
- Memory savings minimal (few duplicates)

**Problem 3: Complex dependency tracking**

Type interning complicates:
- Garbage collection (shared types can't be freed easily)
- Incremental re-elaboration (invalidating interned types)
- Concurrency (global hash table requires locking)

### What Kovács Does Instead

**smalltt's approach:**
- **No hash consing** for types or values
- **Direct tree representation** (normal forms are trees, closures are closures)
- **Lazy evaluation** (don't compute more than needed)
- **Explicit memoization** where it helps (e.g., top-level definitions)

**Result:** Simpler implementation, competitive performance with Lean/Agda

---

## 2. When Interning DOES Help

### String Interning (Universal)

**All systems intern strings:**
- Names (`foo`, `bar`, `MyModule.MyType`)
- String literals
- Module paths

**Why it works:**
- **High duplication**: Names reused constantly
- **Small keys**: Strings hash quickly
- **Simple comparison**: Pointer equality instead of strcmp

**Implementation:**
```rust
struct InternedString {
    id: u32,  // Index into string table
}

struct StringTable {
    strings: Vec<String>,  // Actual string data
    lookup: HashMap<String, u32>,  // String → ID
}
```

**Savings:** ~60-80% memory reduction for name storage

### Name Interning (Module-qualified names)

```rust
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct QName(u32);  // 4 bytes instead of ~40 bytes for full path

struct QNameTable {
    names: Vec<QualifiedName>,  // Full data
    lookup: HashMap<QualifiedName, u32>,
}

struct QualifiedName {
    module: InternedString,
    name: InternedString,
}
```

**Used by:** Lean, Agda, Coq, Idris

**Benefits:**
- Fast equality checks (integer comparison)
- Compact representation in AST nodes
- Efficient serialization (just write ID, lookup string in table)

### Constant Interning (Top-level definitions)

**What to intern:**
- Global constants (function names, datatype names)
- Constructors
- Axioms/postulates

**Why:**
- Referenced many times throughout module
- Fixed after elaboration (immutable)
- Small deduplication table (dozens to thousands, not millions)

**Lean 4's approach:**
```cpp
struct ConstantInfo {
    Name name;
    TypeExpr type;
    ValueExpr value;  // Or None for axioms
    // ... metadata
};

// Global environment stores constants by name
HashMap<Name, ConstantInfo> constants;
```

---

## 3. Existing Systems: Serialization Strategies

### Lean 4: `.olean` Files (Compact Regions)

**Key innovation:** Compacted heap region

**Structure:**
```
.olean file:
├── Header (magic number, version)
├── Environment data (constants, inductives, etc.)
└── Compacted heap region
    └── All runtime objects needed by environment
```

**Compacted region:**
- Serializes Lean's runtime objects (closures, arrays, etc.)
- Objects laid out contiguously (no pointers, use offsets)
- Can be `mmap()`'d directly into memory (zero-copy loading!)
- Deterministic layout (post-order traversal for reproducibility)

**Implementation details** (from `src/runtime/compact.cpp`):
```cpp
void object_compactor::copy_object(object * o) {
    size_t sz = lean_object_byte_size(o);
    void * mem = alloc(sz);  // Allocate in compact region
    memcpy(mem, o, sz);      // Copy object
    // Convert pointers to offsets
    // ...
}
```

**Benefits:**
- **Fast loading**: `mmap()` + pointer fixup (or no fixup if same address!)
- **Deterministic**: Post-order traversal ensures reproducible serialization
- **Compact**: No per-object headers or padding

**Drawbacks:**
- Complex implementation (pointer → offset conversion)
- Platform-specific (address space layout)
- Large files (whole environment serialized)

**HWML relevance:** Possible future optimization (Phase 3+), not MVP

---

### Agda: `.agdai` Files (Structure Sharing)

**Key innovation:** Explicit structure sharing via memoization tables

**Serialization architecture** (from `Agda.TypeChecking.Serialise.Base`):

```haskell
data Dict = Dict
  { nodeD   :: !(HashTable Node Word32)       -- Shared AST nodes
  , stringD :: !(HashTable Text Word32)       -- Interned strings
  , integerD :: !(HashTable Integer Word32)   -- Integer literals
  , doubleD :: !(HashTable Double Word32)     -- Double literals
  , nameD   :: !(HashTable NameId Word32)     -- Qualified names
  , qnameD  :: !(HashTable QNameId Word32)    -- Qualified names
  }

class EmbPrj a where
  icode :: a -> S Word32  -- Serialize to ID
  value :: Word32 -> R a  -- Deserialize from ID
```

**Serialization process:**
1. Traverse AST
2. For each node: check if already serialized (via `nodeD` table)
3. If yes: write ID only
4. If no: serialize full node, assign ID, insert into table

**What gets shared:**
- AST nodes (expressions, types, declarations)
- Strings and names (always)
- Literal values (integers, doubles)

**What doesn't get shared:**
- Ranges/positions (always serialized as `noRange` to save space)
- Transient metadata (only logical content)

**Benefits:**
- Significant space savings (~50-70% reduction)
- Reasonable serialization speed (memoization avoids re-traversal)
- Platform-independent (just IDs + data tables)

**Drawbacks:**
- Serialization time overhead (hashtable lookups)
- Deserialization builds entire structure (can't lazy-load)
- Large memory footprint during serialization (live + memo tables)

**Agda's pragmatic choice:**
```haskell
-- Memoize A.Name saves ~17% serialization time (25s -> 21s for std-lib)
-- Per Andreas Able's comment in source code
nameD :: !(HashTable NameId Word32)  -- Memoized
```

---

### Coq: `.vo` Files (OCaml Marshaling)

**Key approach:** OCaml's built-in `Marshal` module

**Structure:**
```
.vo file:
├── Magic number (version check)
├── Segments (named sections):
│   ├── "summary" (module dependencies)
│   ├── "library" (compiled definitions)
│   ├── "opaques" (proof objects)
│   └── "tasks" (async proof tasks)
└── Checksums for each segment
```

**Serialization:**
```ocaml
(* From ObjFile module *)
val marshal_out_segment : out_handle -> segment:string -> 'a -> unit

(* Uses OCaml's Marshal.to_channel internally *)
(* Automatically handles sharing via built-in object graph traversal *)
```

**OCaml Marshal features:**
- **Automatic sharing**: DAG traversal with hash-consing
- **Type-safe**: Marshals OCaml values (but unsafe on reload!)
- **Versioned**: Magic numbers prevent loading incompatible `.vo` files

**Benefits:**
- Simple to use (just `Marshal.output`)
- Automatic sharing (OCaml runtime handles it)
- Fast serialization

**Drawbacks:**
- **Version brittleness**: Any change to OCaml types breaks `.vo` format
- **Not human-readable**: Binary blob, hard to debug
- **Limited control**: Can't optimize serialization strategy

**Coq's pain points:**
- Frequent `.vo` incompatibility between Coq versions
- Need for tools like `coqchk` to verify `.vo` files
- SerAPI project provides JSON/S-expression alternative

---

### Idris: Portable JSON (Historical)

**Approach:** JSON-based serialization (Idris 1)

```json
{
  "file-type": "idris-codegen",
  "version": "1.0",
  "codegen-info": {
    "interfaces": [...],
    "simple-decls": [...],
    "tt-terms": [...]
  }
}
```

**Benefits:**
- **Portable**: Works across platforms, Idris versions
- **Debuggable**: Human-readable
- **Flexible**: Easy to extend

**Drawbacks:**
- **Slow**: JSON parsing overhead
- **Large files**: Verbose representation
- **No sharing**: Every occurrence serialized separately

**Idris 2:** Switched to binary format (similar to Lean's approach)

---

## 4. What Should HWML Do?

### Core Principle: Types Are Values

In HWML (like all dependently typed languages):
```rust
// This is a value AND a type:
fn identity<A: Type>(x: A) -> A { x }

// The type (A: Type) -> A is computed at elaboration time
// It's a *value* in the type universe
```

**Implication:** We need one serialization strategy that works for both types and values.

### Recommended Approach: Hybrid

**Intern aggressively:**
1. **Strings** (names, literals)
   ```rust
   struct StringId(u32);
   struct StringTable { /* ... */ }
   ```

2. **Qualified names** (module paths + local names)
   ```rust
   struct QName(u32);
   struct QNameTable { /* ... */ }
   ```

3. **Global constants** (top-level definitions)
   ```rust
   struct ConstId(u32);
   struct ConstTable {
       constants: Vec<Declaration>,  // Full elaborated declarations
       lookup: HashMap<QName, ConstId>,
   }
   ```

**Do NOT intern:**
1. **Types** (too unique, overhead > benefit)
2. **Values** (closures, computed values)
3. **Elaborated expressions** (except via structure sharing)

**Use structure sharing (Agda-style) for:**
- AST nodes during serialization (detect shared subexpressions)
- Large repeated subterms (but don't force it)

### `.hwmli` Format Design

```rust
pub struct Hwmli {
    // === Header ===
    version: u32,
    hwml_compiler_hash: Blake3Hash,  // Invalidates on compiler change

    // === Interning Tables ===
    strings: StringTable,       // All strings (names, literals)
    qnames: QNameTable,         // Qualified names

    // === Library Metadata ===
    library_name: QName,
    dependencies: Vec<Dependency>,

    // === Declarations ===
    declarations: Vec<Declaration>,

    // === Early Cutoff Support (Phase 4) ===
    export_interface_hash: Blake3Hash,
    declaration_fingerprints: HashMap<DeclId, Blake3Hash>,
    usage_map: HashMap<QName, HashSet<DeclId>>,
}

pub enum Declaration {
    Constant {
        name: QName,
        type_expr: Expr,
        value: Option<Expr>,  // None for axioms/postulates
        source_location: SourceRange,
    },
    Inductive {
        name: QName,
        type_params: Vec<(QName, Expr)>,
        constructors: Vec<Constructor>,
    },
}

pub enum Expr {
    Var(DeBruijnIndex),
    Global(ConstId),  // Reference to constant (interned)
    App(Box<Expr>, Box<Expr>),
    Lam(QName, Box<Expr>, Box<Expr>),  // name, type, body
    Pi(QName, Box<Expr>, Box<Expr>),   // name, domain, codomain
    Let(QName, Box<Expr>, Box<Expr>, Box<Expr>),  // name, type, value, body
    Universe(Level),
    // ... other constructors
}
```

**Key design decisions:**

1. **`Expr` NOT interned**: Each expression is a tree
   - Simple to implement (no hashtables during elaboration)
   - Follows Kovács' advice
   - Overhead: ~10-20% more memory, but simpler code

2. **`Global(ConstId)` IS interned**: References to top-level constants
   - High reuse (every usage of `std::Vec` is same `ConstId`)
   - Small table (thousands, not millions)
   - Fast equality (`ConstId` comparison)

3. **Structure sharing during serialization** (optional optimization):
   ```rust
   struct Serializer {
       expr_memo: HashMap<Expr, u32>,  // Detect shared subexpressions
       next_id: u32,
   }

   fn serialize_expr(&mut self, expr: &Expr) -> Result<()> {
       if let Some(id) = self.expr_memo.get(expr) {
           write_tag(SHARED_REF)?;
           write_u32(*id)?;
       } else {
           let id = self.next_id;
           self.next_id += 1;
           self.expr_memo.insert(expr.clone(), id);

           write_tag(EXPR_NODE)?;
           match expr {
               // ... serialize actual expression
           }
       }
       Ok(())
   }
   ```

4. **No Lean-style compact region** (not worth complexity for MVP):
   - Lean's approach requires pointer → offset conversion
   - HWML can use simpler binary encoding
   - Future: Consider compact regions if loading time becomes bottleneck

---

## 5. Serialization Format Details

### Binary Encoding (MessagePack-like)

**Why binary:**
- Compact (50-70% smaller than JSON)
- Fast parsing (no string → number conversions)
- Direct memory mapping possible (future optimization)

**Tag system:**
```rust
enum Tag {
    // Primitives
    SmallInt(u8),      // 0-127 inline
    VarInt,            // Variable-length integer
    String(u32),       // Length-prefixed UTF-8
    StringRef(u32),    // Reference to interned string

    // Expressions
    Var,               // De Bruijn index follows
    Global,            // ConstId follows
    App,               // Function, argument follow
    Lam,               // Name, type, body follow
    Pi,                // Name, domain, codomain follow
    Universe,          // Level follows

    // Structure sharing
    SharedDef(u32),    // Define shared node (ID follows, then node)
    SharedRef(u32),    // Reference to shared node
}
```

**Example encoding:**
```rust
// Expression: λx. x
// Lambda(name: "x", type: Universe(0), body: Var(0))

Tag::Lam
  Tag::StringRef(42)     // "x" (already interned)
  Tag::Universe
    Tag::SmallInt(0)     // Universe level 0
  Tag::Var
    Tag::SmallInt(0)     // De Bruijn index 0
```

**Estimated sizes:**
- Small lambda: ~10-15 bytes
- Type signature: ~30-50 bytes
- Full declaration: ~100-500 bytes

**Compared to JSON:**
```json
{
  "kind": "Lam",
  "name": "x",
  "type": {"kind": "Universe", "level": 0},
  "body": {"kind": "Var", "index": 0}
}
```
→ 115 bytes (vs ~15 bytes binary)

### String Table Format

```rust
struct StringTable {
    count: u32,
    strings: Vec<String>,  // Sorted for binary search during loading
}

// Serialized as:
// <count: u32>
// <string1_len: u32><string1_bytes>
// <string2_len: u32><string2_bytes>
// ...
```

**Optimization:** Sort strings alphabetically for better compression (adjacent strings often share prefixes)

### QName Table Format

```rust
struct QNameTable {
    count: u32,
    names: Vec<(StringId, StringId)>,  // (module, name) pairs
}

// Example:
// std::Vec::new
// → (strings[std::Vec], strings[new])
```

**Benefits:**
- Compact (two u32s per qualified name)
- Module names shared across all names in that module
- Fast equality (compare two u32 pairs)

---

## 6. Comparison: Interning Strategies

| System | Strings | Names | Types | Values | AST Nodes | Rationale |
|--------|---------|-------|-------|--------|-----------|-----------|
| **Lean 4** | ✅ | ✅ | ❌ | ❌ | ❌ | Compact region (whole heap) |
| **Agda** | ✅ | ✅ | ✅ | ✅ | ✅ | Structure sharing (everything) |
| **Coq** | ✅ | ✅ | Auto* | Auto* | Auto* | OCaml Marshal (implicit) |
| **smalltt** | ✅ | ✅ | ❌ | ❌ | ❌ | Explicit anti-interning stance |
| **HWML (proposed)** | ✅ | ✅ | ❌ | ❌ | ⚠️** | Follow Kovács + structure sharing |

*Auto: OCaml's Marshal automatically handles sharing
**⚠️: Optional structure sharing during serialization only (not in-memory)

---

## 7. Recommendations for HWML

### Phase 1: MVP Serialization

**What to implement:**
```rust
// 1. String interning
struct InternedString(u32);
impl Hwmli {
    fn intern_string(&mut self, s: &str) -> InternedString;
    fn get_string(&self, id: InternedString) -> &str;
}

// 2. QName interning
struct QName(u32);
impl Hwmli {
    fn intern_qname(&mut self, module: &str, name: &str) -> QName;
}

// 3. Binary serialization (no structure sharing yet)
fn serialize_expr(expr: &Expr, writer: &mut impl Write) -> Result<()> {
    match expr {
        Expr::Var(idx) => {
            write_tag(Tag::Var)?;
            write_varint(*idx)?;
        }
        Expr::Global(const_id) => {
            write_tag(Tag::Global)?;
            write_u32(const_id.0)?;
        }
        // ... etc
    }
}
```

**Complexity:** ~500-1000 lines of code

**Benefits:**
- Simple, easy to debug
- Follows Kovács' advice (no premature optimization)
- Strings/names interned (high-value, low-complexity)

### Phase 2: Structure Sharing (Optional Optimization)

**If profiling shows duplication:**
```rust
struct Serializer {
    expr_cache: HashMap<Expr, u32>,
    next_id: u32,
}

fn serialize_expr_with_sharing(&mut self, expr: &Expr) -> Result<()> {
    if let Some(id) = self.expr_cache.get(expr) {
        write_tag(Tag::SharedRef)?;
        write_u32(*id)?;
        return Ok(());
    }

    let id = self.next_id;
    self.next_id += 1;
    write_tag(Tag::SharedDef)?;
    write_u32(id)?;
    self.expr_cache.insert(expr.clone(), id);

    // Serialize actual expression
    // ...
}
```

**When to enable:**
- If `.hwmli` files >10MB (likely won't happen initially)
- If profiling shows >30% duplicate subexpressions
- After MVP is working

### Phase 3: Compact Regions (Future)

**Lean-style optimization:**
- Serialize whole heap as compact region
- `mmap()` into memory (zero-copy)
- Requires pointer → offset conversion
- **Only if** loading time becomes bottleneck (unlikely for <100kloc projects)

---

## 8. Implementation Plan

### Crate Structure

```
hwml-object-format/
├── src/
│   ├── lib.rs           # Public API
│   ├── intern.rs        # String/QName interning
│   ├── format.rs        # Binary encoding/decoding
│   ├── expr.rs          # Expression serialization
│   └── hwmli.rs         # Top-level .hwmli structure
└── tests/
    ├── roundtrip.rs     # Serialize → deserialize → compare
    └── compat.rs        # Version compatibility tests
```

### API Example

```rust
// Serialization
let mut hwmli = Hwmli::new();
hwmli.library_name = hwmli.intern_qname("myproject", "Main");

for decl in elaborated_declarations {
    hwmli.add_declaration(decl);
}

let bytes = hwmli.serialize()?;
fs::write("myproject.hwmli", bytes)?;

// Deserialization
let bytes = fs::read("myproject.hwmli")?;
let hwmli = Hwmli::deserialize(&bytes)?;

// Fast constant lookup
let vec_new_id = hwmli.lookup_constant("std::Vec", "new")?;
let vec_new_type = hwmli.get_constant(vec_new_id).type_expr;
```

---

## 9. Success Metrics

**Phase 1 (MVP):**
- [ ] Serialize/deserialize round-trip (byte-identical after round-trip)
- [ ] .hwmli files <5x source file size
- [ ] Deserialization <100ms for 10kloc library
- [ ] String interning reduces name storage by >60%

**Phase 2 (Optimized):**
- [ ] .hwmli files <2x source file size
- [ ] Deserialization <50ms for 10kloc library
- [ ] Structure sharing reduces file size by >30% (if enabled)

**Phase 3 (Production):**
- [ ] Compact regions (if needed) reduce loading to <10ms
- [ ] `.hwmli` files compatible across HWML versions (with version check)
- [ ] CAS deduplication works correctly with .hwmli hashes

---

## References

### Systems Studied
- **Lean 4**: https://github.com/leanprover/lean4
  - `src/runtime/compact.cpp` (compact regions)
  - `.olean` format (environment serialization)
- **Agda**: https://github.com/agda/agda
  - `Agda.TypeChecking.Serialise` (structure sharing)
  - `.agdai` format
- **Coq**: https://github.com/coq/coq
  - `ObjFile` module (segment-based `.vo`)
  - OCaml Marshal
- **smalltt**: https://github.com/AndrasKovacs/smalltt
  - README (anti-interning argument)

### Papers
- Kovács, "Elaboration with First-Class Implicit Function Types", ICFP 2020
- Chapman et al., "Type Theory Should Eat Itself", ICFP 2019 (Epigram)
- "Efficient Communication and Collection with Compact Normal Forms" (Lean's mmap inspiration)

---

**Next Steps:**
1. Design `.hwmli` binary format (tag system, layouts)
2. Implement string/QName interning in `hwml-db`
3. Prototype serialization for `Expr` type
4. Measure baseline: file sizes, serialization speed
5. Add structure sharing if profiling shows benefit

**Key Takeaway:** Keep it simple. Intern strings/names/constants. Don't intern types/values. Add structure sharing only if measurements prove it's needed.
