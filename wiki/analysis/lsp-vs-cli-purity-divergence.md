# Analysis: LSP vs CLI Purity Divergence and `.hwmli` Contents

**Date:** 2026-05-04  
**Status:** Critical architecture clarification  
**Related:** [[decisions/ADR-007-salsa-driven-compilation]], [[decisions/ADR-009-rkyv-zero-copy-serialization]], [[analysis/compiler-package-manager-build-system-separation]], [[research/buck2-integration-patterns]]

---

## Executive Summary

**Critical Issue Identified:** The LSP and CLI must operate fundamentally differently while sharing the same core compiler (`hwml-db` + `hwml-elab`).

**Key Insight:** Reading from a compilation cache is only "impure" if done **secretly behind Buck2's back**. When Buck2 explicitly provides `.hwmli` files via sandbox inputs and `--extern` flags, this is **mathematically pure**.

**Architecture Requirement:** The compiler core must accept explicit external dependencies without doing any file discovery. This allows:
- **LSP:** Stateful, discovers files, uses local cache
- **CLI (Buck2):** Pure, no discovery, only processes explicit inputs

---

## The Purity Problem

### What is "Impure" (Breaks Buck2)

❌ **BAD: Compiler secretly reads global cache**

```rust
// Inside hwml-elab
fn resolve_import(name: &str) -> Result<Library> {
    // ❌ IMPURE: Secretly looks in hidden directory
    let cache_path = format!("~/.hwml_cache/{}.hwmli", name);
    if let Ok(cached) = read_hwmli(cache_path) {
        return Ok(cached);
    }
    // Buck2 cannot track this!
}
```

**Why this breaks:**
1. Buck2 doesn't know about `~/.hwml_cache/`
2. Different machines have different cache contents
3. Non-deterministic builds (cache hit vs miss)
4. Sandbox cannot prevent this (directory exists outside)

### What is "Pure" (Buck2 Compatible)

✅ **GOOD: Buck2 provides dependencies explicitly**

```bash
# Buck2 creates sandbox: /tmp/sandbox_123/
# Maps inputs explicitly:
#   /tmp/sandbox_123/src/uart.hwml
#   /tmp/sandbox_123/deps/fifo.hwmli

# Runs compiler with explicit paths
$ hwmlc compile src/uart.hwml \
    --extern Fifo=deps/fifo.hwmli \
    --extern Std=deps/std.hwmli \
    --out buck-out/uart.hwmli
```

**Why this is pure:**
1. Buck2 controls all inputs (sandboxed)
2. Compiler receives explicit paths (no discovery)
3. Deterministic: `(Source, Externs) -> Output`
4. Buck2 can hash and cache the action

---

## The Buck2 Execution Model

### Step-by-Step: How Buck2 Compiles Uart (depends on Fifo)

**1. Wait for Dependencies**

Buck2 builds dependency graph:
```
Fifo (no deps) → Uart (depends on Fifo)
```

Buck2 executes `Fifo` action first:
```bash
$ hwmlc compile src/fifo.hwml --out buck-out/fifo.hwmli
```

Result: `buck-out/.../fifo.hwmli` (pure artifact)

**2. Create Sandbox**

Buck2 creates isolated directory: `/tmp/sandbox_abc123/`

**3. Map Inputs**

Buck2 hardlinks/symlinks ONLY declared inputs:
```
/tmp/sandbox_abc123/
├── src/
│   └── uart.hwml        (source file)
└── deps/
    ├── fifo.hwmli       (compiled artifact from step 1)
    └── std.hwmli        (from remote cache or previous build)
```

**Key:** Sandbox contains NOTHING ELSE. No `~/.hwml_cache/`, no system libs, nothing.

**4. Execute**

```bash
$ hwmlc compile src/uart.hwml \
    --extern Fifo=deps/fifo.hwmli \
    --extern Std=deps/std.hwmli \
    --out buck-out/uart.hwmli
```

**Inside compiler:**
```rust
// Parse CLI args
let externs = vec![
    ("Fifo", PathBuf::from("deps/fifo.hwmli")),
    ("Std", PathBuf::from("deps/std.hwmli")),
];

// Load externs into Salsa
for (name, path) in externs {
    let hwmli = read_hwmli(path)?;  // ✅ Explicit path
    db.set_library_interface(name, hwmli);
}

// Elaborate uart
elaborate_library(db, "src/uart.hwml")
```

**Result:** Pure function. Same inputs → same output. Always.

---

## Architectural Divergence: LSP vs CLI

### LSP: Stateful File Discovery

**Purpose:** Fast, interactive, user-friendly IDE experience

**Behavior:**

```rust
// LSP initialization
impl LanguageServer for HwmlLsp {
    fn initialize(&mut self, params: InitializeParams) {
        let workspace_root = params.root_uri.to_file_path();

        // 1. Read hwml-workspace.toml (file discovery)
        let workspace = discover_workspace(&workspace_root);

        // 2. Load .hwml/resolved-deps.json (path mapping)
        let resolved = load_resolved_deps(&workspace_root);

        // 3. For each library, try to load from cache
        for (name, manifest) in workspace.libraries {
            let cache_path = format!("~/.hwml/cache/{}.hwmli", name);

            if let Some(cached) = load_hwmli_if_valid(&manifest, &cache_path) {
                // ✅ Cache hit: deserialize into Salsa
                db.set_library_interface(name, cached);
            } else {
                // ❌ Cache miss: elaborate from source
                elaborate_library(&db, &manifest)?;
            }
        }

        // 4. Watch files for changes
        watch_workspace_files(&workspace_root);
    }
}
```

**Characteristics:**
- ✅ **Stateful:** Reads `hwml.toml`, discovers files, scans directories
- ✅ **Caching:** Uses local cache (`~/.hwml/cache/`) for performance
- ✅ **Fallback:** Falls back to source if cache miss
- ✅ **Dynamic:** Responds to file changes, updates incrementally
- ⚠️ **Impure:** But that's OK — LSP is for humans, not Buck2

---

### CLI (Buck2 Mode): Pure, Explicit

**Purpose:** Deterministic, hermetic, cacheable builds

**Behavior:**

```rust
// CLI invocation by Buck2
fn main() {
    let args = parse_args();  // --extern, --out, source files

    // NO file discovery
    // NO reading hwml.toml
    // NO cache lookups

    let db = HwmlDatabase::new();

    // Load ONLY explicitly provided dependencies
    for (name, path) in args.externs {
        let hwmli = read_hwmli(&path)?;  // Explicit path from Buck2
        db.set_library_interface(name, hwmli);
    }

    // Compile ONLY explicitly provided sources
    for source_file in args.sources {
        elaborate_file(&db, &source_file)?;
    }

    // Write output to explicit path
    write_hwmli(&args.output, &result)?;
}
```

**Characteristics:**
- ✅ **Pure:** No file discovery, no ambient state
- ✅ **Explicit:** All inputs via CLI args
- ✅ **Sandboxed:** Only sees files Buck2 provides
- ✅ **Deterministic:** Same inputs → same output
- ✅ **Cacheable:** Buck2 can hash and cache the action

---

### The Shared Core: `hwml-db` + `hwml-elab`

**Key Design Requirement:** Core compiler must support BOTH modes without caring which is calling it.

**Abstraction:**

```rust
// Core trait: Dependency provider (abstract)
pub trait ExternProvider {
    fn get_library(&self, name: &str) -> Result<LibraryInterface>;
}

// LSP implementation: Discovers and caches
struct LspExternProvider {
    workspace: WorkspaceRoot,
    cache: LocalCache,
}

impl ExternProvider for LspExternProvider {
    fn get_library(&self, name: &str) -> Result<LibraryInterface> {
        // Try cache first
        if let Some(cached) = self.cache.get(name) {
            return Ok(cached);
        }

        // Fall back to discovering and elaborating
        let manifest = self.workspace.find_library(name)?;
        elaborate_library_from_source(&manifest)
    }
}

// CLI implementation: Only uses explicit paths
struct CliExternProvider {
    externs: HashMap<String, LibraryInterface>,
}

impl ExternProvider for CliExternProvider {
    fn get_library(&self, name: &str) -> Result<LibraryInterface> {
        // Only return if explicitly provided via --extern
        self.externs.get(name)
            .cloned()
            .ok_or_else(|| Error::MissingExtern(name))
    }
}

// Core elaboration (doesn't care which provider)
pub fn elaborate_library<P: ExternProvider>(
    db: &dyn HwmlDb,
    provider: &P,
    source: &SourceFile,
) -> Result<LibraryInterface> {
    // When encountering `import Fifo`, ask provider:
    let fifo_interface = provider.get_library("Fifo")?;

    // Continue elaboration...
}
```

**Benefit:** Same core code, different providers, both pure at their level.

---

## CLI Interface Design

### Required CLI Flags

**For Buck2 compatibility, HWML compiler needs:**

```bash
$ hwmlc compile <SOURCE> \
    --extern <NAME>=<PATH> \
    --out <OUTPUT> \
    --dep-file <DEPFILE> \
    [--message-format json]
```

**Example:**

```bash
$ hwmlc compile src/uart.hwml \
    --extern Fifo=deps/fifo.hwmli \
    --extern Std=deps/std.hwmli \
    --out buck-out/uart.hwmli \
    --dep-file buck-out/uart.d \
    --message-format json
```

**Flag meanings:**

1. **`--extern NAME=PATH`** (repeatable)
   - Provides compiled dependency interface
   - NAME: Import name used in source (`import Fifo`)
   - PATH: Absolute or sandbox-relative path to `.hwmli`
   - Compiler loads this into global namespace

2. **`--out PATH`**
   - Where to write output `.hwmli` file
   - Buck2 controls this path (sandboxed)

3. **`--dep-file PATH`**
   - Write Makefile-style dependency file
   - Lists all files actually read during compilation
   - Buck2 uses this for fine-grained invalidation

4. **`--message-format json`**
   - Emit errors/warnings as JSON
   - Required for Buck2 to parse diagnostics correctly

**Dep file format:**

```makefile
# uart.d
buck-out/uart.hwmli: \
    src/uart.hwml \
    src/impl.hwml \
    deps/fifo.hwmli \
    deps/std.hwmli
```

Buck2 uses this to know: "Only rebuild `uart.hwmli` if one of these files changed."

---

## What Goes in `.hwmli` Files?

**Critical Question:** What must be serialized for downstream compilation?

### Option 1: Signatures Only (Monomorphized World)

**Serialize:** Only concrete, fully-elaborated type signatures

**Example:**

```hwml
// In fifo.hwml
pub fn new<T>(capacity: Nat) -> Fifo<T> { ... }
pub fn push<T>(fifo: &mut Fifo<T>, item: T) { ... }
```

**In `fifo.hwmli`:**
```rust
// Serialized signatures (concrete after elaboration)
pub fn new: (capacity: Nat) -> ∀T. Fifo<T>
pub fn push: ∀T. (fifo: &mut Fifo<T>, item: T) -> Unit
```

**Downstream compilation (`uart.hwml`):**

```hwml
import Fifo

fn setup() {
    let fifo: Fifo<u8> = Fifo::new(16);  // Uses signature from fifo.hwmli
    Fifo::push(&mut fifo, 0x42);
}
```

**Problem:** ❌ **This doesn't work for dependent types!**

In HWML, types can depend on **values**. The compiler needs the full term to compute types.

```hwml
// In vec.hwml
pub fn new<T, N: Nat>() -> Vec<T, N> { ... }

// In uart.hwml
import Vec

fn setup() {
    let buffer: Vec<u8, 16> = Vec::new();
    //                   ^^
    // Type depends on VALUE 16
    // Compiler needs to run type-level computation
}
```

To type-check this, the compiler needs to know:
- What is `Vec::new`'s type?
- Answer: `∀T, N: Nat. Vec<T, N>`
- But to check `Vec::new()` at callsite, it needs to:
  1. Infer `T = u8` (from annotation)
  2. Infer `N = 16` (from annotation)
  3. **Substitute** into return type: `Vec<u8, 16>`

**Issue:** For dependent types, "signatures" aren't enough. You need **parametric terms**.

---

### Option 2: Parametric Terms (Full Elaboration)

**Serialize:** Typed, elaborated core terms (not raw AST, but after type-checking)

**In `fifo.hwmli`:**

```rust
pub struct Fifo<T> {
    buffer: Vec<T, capacity>,  // Dependent on capacity parameter
    capacity: Nat,
    head: Nat,
    tail: Nat,
}

pub fn new<T>(capacity: Nat) -> Fifo<T> {
    // Elaborated core term (not raw AST)
    // Includes:
    //   - Type signature: (capacity: Nat) -> Fifo<T>
    //   - Body term (for type-level computation if needed)
    //   - Metadata (source location, etc.)

    Fifo {
        buffer: Vec::new<T, capacity>(),  // Type depends on capacity
        capacity: capacity,
        head: 0,
        tail: 0,
    }
}
```

**Downstream compilation:**

When `uart.hwml` calls `Fifo::new(16)`:
1. Load `Fifo::new` term from `fifo.hwmli`
2. Type is `(capacity: Nat) -> Fifo<T>`
3. Apply argument `16`: substitute `capacity := 16`
4. Return type becomes `Fifo<T>` where `T` is inferred as `u8`
5. Body is NOT executed (monomorphization happens later in codegen)

**What gets serialized:**

```rust
pub struct LibraryInterface {
    // Public definitions
    pub definitions: HashMap<QualifiedName, Definition>,
}

pub struct Definition {
    pub name: QualifiedName,
    pub type_signature: Term,      // Fully elaborated type
    pub body: Option<Term>,         // Elaborated term (for parametric functions)
    pub attributes: Attributes,     // pub, inline, etc.
    pub source_location: SourceLoc,
}

pub enum Term {
    // Core language (post-elaboration)
    Var(DeBruijnIndex),
    Global(ConstantId),
    App(Box<Term>, Box<Term>),
    Lam { param: Term, body: Term },  // λx:A. b
    Pi { domain: Term, codomain: Term },  // (x: A) -> B
    Let { binding: Term, value: Term, body: Term },
    Universe(Level),
    // Hardware-specific
    Module { ports: Vec<Port>, body: Term },
    Register { width: Nat, init: Term },
    // ...
}
```

**Key:** This is **elaborated core**, not surface AST.
- Types are checked
- Implicits are resolved
- Metavariables are solved
- Unification is done

**Benefits:**
- ✅ Supports dependent types (types depend on values)
- ✅ Allows type-level computation
- ✅ Enables parametric polymorphism
- ✅ Compact (core is smaller than surface)

**Drawbacks:**
- ⚠️ Larger than signatures-only
- ⚠️ Requires re-normalization downstream

---

### Option 3: Hybrid (Signatures + Selective Bodies)

**Serialize:**
- **Always:** Type signatures (for all definitions)
- **Selectively:** Bodies (only for parametric/dependent functions)

**Heuristic:**

```rust
fn should_serialize_body(def: &Definition) -> bool {
    // Serialize body if:
    def.type_signature.is_parametric()  // Has type parameters
        || def.type_signature.is_dependent()  // Type depends on values
        || def.has_attribute("inline")  // Explicitly inlined
}
```

**Example:**

```hwml
// In fifo.hwml

// Parametric: serialize body
pub fn new<T>(capacity: Nat) -> Fifo<T> { ... }

// Concrete: signature only
pub fn is_empty(fifo: &Fifo<u8>) -> Bool { ... }

// Dependent: serialize body
pub fn buffer_of<T, N: Nat>(fifo: &Fifo<T>) -> Vec<T, N> { ... }
```

**In `fifo.hwmli`:**

```rust
// new: parametric → full term
Definition {
    name: "new",
    type_signature: (capacity: Nat) -> ∀T. Fifo<T>,
    body: Some(<elaborated term>),
}

// is_empty: concrete → signature only
Definition {
    name: "is_empty",
    type_signature: (fifo: &Fifo<u8>) -> Bool,
    body: None,  // Don't need body for type-checking downstream
}
```

**Benefits:**
- ✅ Smaller files (don't serialize unnecessary bodies)
- ✅ Still supports dependent types
- ✅ Fast type-checking (only load what's needed)

---

## Recommendation

**Use Option 2 (Parametric Terms) for MVP, optimize to Option 3 later.**

**Rationale:**

1. **HWML is dependently typed:** Types depend on values, so signatures alone are insufficient

2. **Correctness first:** Serialize everything, optimize later

3. **Size is acceptable:**
   - Standard library: ~10MB of `.hwmli` files (compressed)
   - User libraries: ~100KB-1MB each
   - Remote cache makes this fast

4. **Optimization path clear:** Can add Option 3 (selective serialization) as a refinement

**What to serialize (MVP):**

```rust
pub struct Hwmli {
    // Library metadata
    pub name: QualifiedName,
    pub version: Version,
    pub source_hash: Blake3Hash,

    // Public interface
    pub exports: HashMap<String, Definition>,

    // Re-exported definitions (from dependencies)
    pub reexports: HashMap<String, QualifiedName>,
}

pub struct Definition {
    pub name: QualifiedName,
    pub type_signature: Term,  // Fully elaborated type
    pub body: Term,            // Elaborated core term
    pub visibility: Visibility,  // pub, pub(crate), private
    pub attributes: Vec<Attribute>,  // inline, no_mangle, etc.
}
```

**Serialization format:**
- Use `rkyv` (ADR-009: zero-copy deserialization)
- BLAKE3 hash for cache key
- Compress with zstd (10x reduction, negligible CPU cost)

---

## Implementation Checklist

### Phase 1: Pure CLI Mode

**Goal:** Buck2-compatible hermetic compilation

- [ ] Add `--extern NAME=PATH` flag parsing
- [ ] Add `--out PATH` flag
- [ ] Add `--dep-file PATH` flag
- [ ] Add `--message-format json` flag
- [ ] Implement `CliExternProvider` (no file discovery)
- [ ] Serialize full parametric terms to `.hwmli`
- [ ] Test: Compile without reading `hwml.toml`

### Phase 2: LSP Stateful Mode

**Goal:** Fast, cache-friendly IDE experience

- [ ] Implement `LspExternProvider` (with discovery)
- [ ] Add local cache support (`~/.hwml/cache/`)
- [ ] Add cache validation (source hash check)
- [ ] Test: Cold start <2s for 50 libraries

### Phase 3: Buck2 Integration

**Goal:** Production distributed builds

- [ ] Write Buck2 rules (`hwml_library()`)
- [ ] Integrate with REapi v2 (remote cache)
- [ ] Test: Remote cache hit rate >90%

---

## Summary

**Critical Insight:** LSP and CLI are fundamentally different, and that's correct.

- **LSP:** Stateful, discovers files, uses cache (for UX)
- **CLI:** Pure, explicit inputs, sandboxed (for Buck2)

**Both share the same core** (`hwml-db` + `hwml-elab`) via abstraction (`ExternProvider` trait).

**`.hwmli` contents:** Parametric terms (full elaborated core) to support dependent types.

**Next Steps:**
1. Implement `--extern` CLI flag handling
2. Design `ExternProvider` trait
3. Serialize parametric terms to `.hwmli`
4. Test pure CLI mode (no `hwml.toml` reading)
