# LSP & Object File Format Research for HWML

## Overview

Research into how major programming languages with advanced LSP features store
and leverage compiled metadata to enable powerful IDE capabilities.

---

## Key Findings by Language

### 1. **Rust (rust-analyzer)**

**Approach**: In-memory incremental computation (Salsa) + persistent HIR
**Status**: No persistent cache (open issue #4712)

**Architecture**:
- **Salsa**: In-process incremental query engine with memoization
- **HIR (High-level IR)**: Three-layer representation
  - `hir-expand`: Macro expansion
  - `hir-def`: Definitions, item trees, name resolution
  - `hir-ty`: Type inference results
- **ItemTree**: Per-file intermediate format, stored in Salsa database
- **No `.rlib` reuse for IDE**: Compiler artifacts not used by rust-analyzer

**Per-File Metadata**:
```rust
pub struct ItemTree {
    top_level: SmallVec<[ModItem; 1]>,
    attrs: FxHashMap<AttrOwner, RawAttrs>,
    data: Option<Box<ItemTreeData>>,
}
```

**Incremental Strategy**:
- **Early cutoff**: If query output unchanged, downstream not re-evaluated
- **Durability levels**: `volatile` (project files) vs `durable` (stdlib)
- **No cross-session persistence**: All in RAM, rebuilt on restart

**Lessons**:
- Salsa's in-process memoization is extremely effective for LSP use cases
- Persistent cache (#4712) planned but not yet implemented (startup cost acceptable)
- Fine-grained query-based invalidation more important than disk serialization
- Separation of concerns: `hir` provides stable API facade over compiler internals

---

### 2. **Haskell (GHC / HLS)**

**Approach**: `.hi` (interface files) + `.hie` (extended IDE info)
**Status**: Production, used at scale

**.hi files** (GHC interface files):
- Binary format containing:
  - Exported type signatures
  - Data type definitions
  - Strictness information
  - Inlining candidates
- **Not sufficient for IDE features** (goto-definition limited to exports)
- Version-locked to GHC binary (must match exactly)

**.hie files** (Haskell IDE Engine):
```haskell
data HieFile = HieFile {
    hie_hs_file :: FilePath,
    hie_module :: Module,
    hie_types :: Array TypeIndex HieTypeFlat,  -- Type table (deduped)
    hie_asts :: HieASTs TypeIndex,             -- Typed AST with spans
    hie_exports :: [AvailInfo],
    hie_hs_src :: ByteString,                  -- Original source
    hie_entity_infos :: NameEntityInfo         -- Identifier metadata
}
```

**Key Features**:
- **Typed AST**: Every node annotated with source positions and types
- **Scope information**: Identifiers annotated with binding sites
- **Efficient type sharing**: `Array TypeIndex HieTypeFlat` deduplicates types
- **LSIF generation**: `.hie` files can generate Language Server Index Format
- **Cross-module goto-definition**: Works without recompiling dependencies

**File relationships**:
- `A.hs` → `A.hi` (for importing modules)
- `A.hs` → `A.hie` (for IDE features)
- HLS uses `.hie` for goto-def, hover, find-references
- Falls back to `.hi` when `.hie` unavailable (degraded experience)

**Lessons**:
- Separate "compilation interface" (`.hi`) from "IDE interface" (`.hie`)
- Raw source bytes in `.hie` enable error messages without re-reading files
- Type deduplication via array indexing crucial for payload size
- Must be generated during compilation (can't reconstruct from `.hi` alone)

---

### 3. **OCaml (Merlin)**

**Approach**: File-based caching with `File_id` invalidation
**Status**: Production, mature

**.cmi files** (Compiled Module Interfaces):
- Standard OCaml compiler output
- Contain type signatures of exported definitions
- Cached by Merlin via `File_cache.Make(Cmi_format)`

**.cmt/.cmti files** (Compiled Module Typedtree):
```ocaml
type cmt_infos = {
  cmt_modname : Compilation_unit.t;
  cmt_annots : binary_annots;  (* Typed AST *)
  cmt_value_dependencies : ...;
  cmt_shape : ...;              (* For jump-to-definition *)
}
```

**Caching Architecture** (`doc/dev/CACHING.md`):

**File_id**: Content-addressed file identity
```ocaml
File_id.get filename   (* Compute hash+mtime *)
File_id.check id       (* True if unchanged *)
```

**File_cache functor**:
```ocaml
module Cmi_cache = File_cache.Make(Cmi_format)
module Cmt_cache = File_cache.Make(Cmt_format)
```

**Cache invalidation**:
- Existence of file: depends on directory `File_id` (stat parent dir)
- Contents of file: depends on file's own `File_id`
- Quadratic stat() calls mitigated by caching dir existence checks
- `Env.check_state_consistency()` validates entire environment against disk

**Flush policy**:
- Entries unused for 5 minutes removed (`-cache-lifespan` flag)
- Stated after answering query (don't block user)
- Last 5 `Env.t` cached (`Mtyper.cache`)

**Shapes** (newer feature):
- `.cms/.cmsi` files: lighter than `.cmt`, sufficient for Merlin
- Shape = abstract description of module structure
- `Uid.t` = unique ID per declaration (enables jump-to-def)
- Reduces dependency on full typed AST for code navigation

**Lessons**:
- File-based caching with content hashing works well for long-running LSP
- Separate existence checks from content checks (performance)
- Lazy GC (time-based eviction) prevents unbounded memory growth
- Shapes abstraction: compile once, use for IDE without full typechecking

---

### 4. **Lean 4**

**Approach**: `.olean` (compiled output) + incremental snapshots
**Status**: Production

**.olean files**:
- Required for all imported modules (can't import `.lean` without compiling)
- Contain elaborated terms (full dependent type information)
- Server uses `lake setup-file` to rebuild/locate dependencies

**Incremental compilation**:
- **Snapshots**: Worker maintains snapshots of file state
- **String diffing**: `String.firstDiffPos` finds first changed position
- Only reprocess file from first change downward (line-based granularity)
- Persistent data structures for efficient snapshot forking

**.ilean files** (newer):
- Lightweight index files for find-references
- Watchdog loads all `.ilean` on startup (bundle-free architecture)
- Enables project-wide references without holding full `.olean` in memory

**LSP Architecture**:
- Separate **watchdog** process + per-file **workers**
- Workers communicate via `LEAN_PATH` to locate `.olean` dependencies
- Snapshot chain: each edit creates new snapshot linked to previous
- On file save: rebuilds and refreshes dependencies

**Lessons**:
- For dependent types, you MUST cache elaborated terms, not just types
- Incremental within-file: snapshot chain with structural sharing
- `.ilean` demonstrates split between "compilation artifact" and "index"
- Line-based incremental good enough (no need for fine-grained AST diffing)

---

### 5. **Agda**

**Approach**: `.agdai` (interface files) with aggressive caching
**Status**: Production

**.agdai files**:
- Contain results of type-checking:
  - Resolved implicit arguments
  - Pattern-matching translated to case trees
  - Compressed expression trees (sharing via serialization)
- Loaded for external modules, bypassing type-checking

**Cache behavior**:
- `File_cache` checks `include` directories against cached state
- If include path changes, prune incompatible cached interfaces
- Aggressive structural sharing during serialization (memory efficiency)

**Scope checking vs Type checking**:
- Agda LSP prototype uses **scope checking only** for fast feedback
- Full type-checking deferred until necessary
- Scope info sufficient for: basic completions, jump-to-definition (local)

**Lessons**:
- Compression + sharing critical for dependent type elaboration artifacts
- Two-tier approach: scope-check fast path, type-check slow path
- Include path changes = major invalidation event (not incremental)
- Agdai files intentionally do NOT have stable cross-version format

---

### 6. **Scala (Metals / SemanticDB)**

**Approach**: SemanticDB (separate index format) + Bloop (build server)
**Status**: Production at Twitter scale

**SemanticDB**:
- Language-agnostic protobuf format for semantic information
- Decouples producers (compilers) from consumers (IDEs)
- Generated during batch compilation as side-channel

**TextDocument structure** (protobuf):
```protobuf
message TextDocument {
  string uri = 2;
  string text = 3;                          // Optional full source
  string md5 = 11;                          // Fingerprint
  repeated SymbolInformation symbols = 5;   // Symbol table
  repeated SymbolOccurrence occurrences = 6; // Name resolution
  repeated Diagnostic diagnostics = 7;
  repeated Synthetic synthetics = 12;        // Compiler-generated trees
}
```

**Symbol format**:
- Global symbols: `scala/Int#`, `scala/Predef.implicitly().(e)`
- Local symbols: `local0`, `local1+2` (unique within document)
- Qualified paths encode package structure

**Type representation**:
- `TypeRef(prefix, symbol, type_arguments)`
- `StructuralType(tpe, declarations)` with hardlinked members
- Full Scala type system (path-dependent, existential, higher-kinded)

**SymbolOccurrence**:
```protobuf
message SymbolOccurrence {
  Range range = 1;
  string symbol = 2;
  Role role = 3;  // REFERENCE or DEFINITION
}
```

**Synthetics** (implicit elaborations):
- Implicit conversions: `"fooo" → augmentString("fooo")`
- Inferred type applications: `List(1).map → map[Int, List[Int]]`
- For-comprehension desugarings

**Build Server Protocol integration**:
- Metals uses BSP to get compilation artifacts from build tool
- Build tool generates SemanticDB during compilation (`-Ysemanticdb`)
- Metals reads SemanticDB for navigation, uses presentation compiler for
  interactivity

**Lessons**:
- **Separate index format** from compiler internals = stability
- Protobuf = language-agnostic, versionable, evolvable
- Storing both symbols AND occurrences enables global find-references
- Synthetics critical for understanding elaborated code
- Index-while-building: IDE piggybacks on normal compilation

---

### 7. **TypeScript (tsserver)**

**Approach**: In-memory + `.tsbuildinfo` for incremental compilation
**Status**: Production

**.tsbuildinfo files**:
- Incremental compilation metadata for project references
- Contains:
  - Semantic diagnostics per file
  - File dependency graph
  - Compiler options snapshot
- **Not portable** across machines (contains absolute paths)
- Versioned per TypeScript compiler version (invalidated on upgrade)

**In-memory architecture**:
- **DocumentRegistry**: Caches parsed `SourceFile` by (filename, version)
- **Incremental parsing**: Reuses unchanged AST subtrees
- **Program instances**: New program reuses old program's files

**Language service**:
```typescript
interface DocumentRegistry {
  acquireDocument(
    fileName: string,
    version: string,
    snapshot: IScriptSnapshot
  ): SourceFile;

  updateDocument(...): SourceFile;
  releaseDocument(...): void;
}
```

**Caching strategy**:
- Parse trees cached in memory (not serialized)
- On file change: incremental re-parse, reuse unchanged subtrees
- Type checking reuses type information for unchanged files
- `.tsbuildinfo` only for cross-invocation build artifacts, not IDE

**Lessons**:
- For dynamically-typed languages, incremental parsing + type checking sufficient
- `.tsbuildinfo` optimizes batch compilation, not IDE experience
- In-memory caching + structural reuse > disk serialization for LSP
- DocumentRegistry pattern: version-keyed cache of parsed files

---

## Common Patterns Across Languages

### Pattern 1: **Two-Tier Artifact Strategy**

Almost every system separates "compilation output" from "IDE metadata":

| Language | Compilation | IDE/Index |
|----------|-------------|-----------|
| Haskell  | `.hi`       | `.hie`    |
| OCaml    | `.cmi`      | `.cmt` / `.cms` |
| Lean 4   | `.olean`    | `.ilean`  |
| Scala    | `.class` / `.tasty` | `.semanticdb` |
| Rust     | `.rlib`     | *(planned persistent cache)* |

**Why separate?**
- Compilation artifact: what's needed to compile downstream code
- IDE artifact: what's needed for navigation without recompiling
- IDE artifact often larger (contains full AST, source ranges, etc.)
- Compilation can succeed without IDE artifact (CI builds)

### Pattern 2: **Typed AST with Source Ranges**

Every system stores more than just type signatures:

- **Haskell `.hie`**: `HieAST TypeIndex` with `SourcedNodeInfo`
- **OCaml `.cmt`**: `binary_annots` (typed tree)
- **SemanticDB**: `SymbolOccurrence` with `Range`
- **Lean `.olean`**: Full elaborated terms with positions

Required for:
- Hover (show type at cursor position)
- Goto definition (from usage span to definition span)
- Find references (all usage spans of a symbol)
- Rename (update all occurrences)

### Pattern 3: **Content-Addressed Invalidation**

How to know when to reload:

- **OCaml**: `File_id` = `(hash, mtime)`
- **Lean**: String diffing to find first changed position
- **Rust**: Salsa queries track input hashes
- **SemanticDB**: MD5 fingerprint of source

Not file modification time alone (racey, non-portable).

### Pattern 4: **Symbol Table + Occurrences**

Two separate data structures:

**Symbol table** (`SymbolInformation` / symbol metadata):
- Definition site, signature, modifiers
- One entry per symbol
- Maps `Symbol → Metadata`

**Occurrences** (`SymbolOccurrence`):
- Every identifier in source
- Maps `SourceRange → Symbol`
- Many entries per symbol

This enables:
- **Hover**: occurrences → symbol → metadata
- **Goto-def**: occurrences → symbol → symbol table → def location
- **Find-refs**: symbol → occurrences (index by symbol)

### Pattern 5: **Deduplication via Indirection**

To control payload size:

**Haskell**:
```haskell
hie_types :: Array TypeIndex HieTypeFlat
hie_asts :: HieASTs TypeIndex  -- References into type array
```

**SemanticDB**:
```protobuf
repeated Type types;  // Shared pool
TypeRef { Type prefix; string symbol; }  // References
```

**Benefit**: `Vec<TypeIndex>` much smaller than `Vec<Type>` when types repeat.

### Pattern 6: **Hardlinking for Local Symbols**

Problem: How to represent types that mention local symbols?

**Scala structural type**: `AnyRef { def x: Int }`
- Method `x` is not a global symbol (can't reference it from other files)
- But must be part of the type signature

**Solution (SemanticDB)**:
```protobuf
message Scope {
  repeated string symlinks = 1;      // Reference to global symbols
  repeated SymbolInformation hardlinks = 2;  // Embed local symbol metadata
}
```

Hardlinks avoid need to load entire symbol table to understand a type signature.

---

## Recommendations for HWML

Based on the research, here's what HWML's `.hwmli` format should include:

### Core Structure

```rust
.hwmli format:

Header:
  magic: [u8; 5]                "hwmli"
  format_version: u8
  compiler_hash: [u8; 32]       SHA-256 of hwml binary
  edition: u32

Source metadata:
  source_hash: [u8; 32]         SHA-256 of original source
  source_text: Option<String>   Optional: include source for error messages

Import table:
  count: u32
  entries: [(library_name: String, export_hash: [u8; 32])]

Symbol table:
  symbols: HashMap<QualifiedName, SymbolInfo>

  where SymbolInfo {
    definition_site: SourceRange,
    signature: Signature,        // Type + value (dependent types!)
    visibility: Visibility,
    documentation: Option<String>,
  }

Type pool:
  types: Vec<Type>               // Deduped type representations

Occurrences:
  occurrences: Vec<Occurrence>

  where Occurrence {
    range: SourceRange,
    symbol: QualifiedName,
    role: Role,                  // Definition | Reference | TypeReference
  }

Elaboration artifacts:
  declarations: Vec<Declaration> // Full elaborated AST (for downstream elab)

Per-declaration fingerprints:
  fingerprints: HashMap<QualifiedName, [u8; 32]>  // GHC-style early cutoff
```

### Required for LSP Features

**For hover**:
- Occurrences: cursor position → symbol
- Symbol table: symbol → signature + documentation
- Type pool: resolve type references to display types

**For goto-definition**:
- Occurrences: cursor position → symbol
- Symbol table: symbol → definition_site SourceRange
- Must preserve library name + file path in SourceRange

**For find-references**:
- Symbol table: definition → symbol
- Occurrences: symbol → all ranges (filter by current workspace)
- Needs cross-file index for workspace-wide search

**For completions**:
- Symbol table: all symbols in scope (from imports + current file)
- Filter by prefix typed
- Show signature in completion item

**For diagnostics**:
- Not stored in `.hwmli` (produced during elaboration)
- But can cache elaboration diagnostics for unopened files

**For rename**:
- Find-references to get all occurrences
- Ensure symbol is not exported (or rename across workspace)
- Rewrite all occurrence ranges

**For document symbols** (outline view):
- Symbol table: filter to symbols defined in this file
- Build tree from qualified name structure
- Include signature in outline

### Serialization Format

**Option 1: Protobuf (like SemanticDB)**

Pros:
- Language-agnostic
- Schema evolution built-in
- Many language bindings
- Standardized

Cons:
- Dependency on protobuf library
- Not as compact as custom binary
- More complex to version

**Option 2: Bincode (Rust)**

Pros:
- Simple, Rust-native
- Very compact
- Fast serialization
- No schema overhead

Cons:
- Rust-only
- Manual versioning required
- Breaking changes require migration code

**Option 3: Custom binary format (like GHC .hi)**

Pros:
- Maximum control over format
- Optimized for exactly our use case
- Can evolve with language

Cons:
- Must implement serialization/deserialization
- More bug surface area
- Hard to debug

**Recommendation**: Start with **Bincode** (serde), add version header for
forward compatibility. Migrate to protobuf if/when non-Rust tools need to
consume `.hwmli` files.

### Lazy Loading Strategy

Not all `.hwmli` content needed immediately:

**On import**:
- Load header (validation)
- Load import table (dependency check)
- Load symbol table (name resolution)
- **Skip** type pool, occurrences, elaboration artifacts

**On goto-definition** (to external library):
- Load symbol table (if not already loaded)
- Locate definition_site, return location

**On hover** (over external library symbol):
- Load symbol table (if not already loaded)
- Load type pool (to resolve symbol's signature)
- Format type for display

**On downstream elaboration**:
- Load full elaboration artifacts (can't avoid this for dependent types)

**Memory-mapped files** (via `memmap2` crate):
```rust
struct LazyHwmli {
    mmap: Mmap,                    // Memory-mapped file
    header: Header,                // Always loaded
    symbol_table_offset: usize,
    symbol_table: OnceCell<SymbolTable>,
    type_pool: OnceCell<Vec<Type>>,
    occurrences: OnceCell<Vec<Occurrence>>,
    // ...
}
```

Lazy initialization on demand, OS handles paging.

---

## LSP-Specific Optimizations

### 1. **Incremental Reparsing** (TypeScript lesson)

When user types:
- Find first changed position (string diff)
- Parse from that position onward
- Reuse unchanged prefix of AST
- For HWML: probably not critical (elaboration dominates parse time)

### 2. **Debouncing** (All LSP servers)

Don't re-elaborate on every keystroke:
- Wait 200-500ms after last edit before re-elaborating
- Cancel in-flight elaboration if new edit arrives
- Show stale diagnostics during typing (mark as stale)

### 3. **Background Indexing** (Metals, rust-analyzer)

On workspace open:
- Load all `.hwmli` files in background thread
- Build workspace-wide symbol index (for find-references, workspace symbol
  search)
- Don't block initial file open on this

### 4. **Partial Elaboration** (Agda lesson)

For diagnostics in current file:
- Elaborate only the current file, treat imports as black boxes (use `.hwmli`)
- Faster feedback than full elaboration

For downstream files:
- Need full elaboration artifacts (dependent types)

### 5. **Cross-file Caching** (Salsa lesson)

Use Salsa-style queries:
```rust
#[salsa::tracked]
fn elaborate_file(db: &dyn Db, file: SourceFile) -> Vec<Declaration> {
    // ...
}

#[salsa::tracked]
fn symbol_at_position(db: &dyn Db, file: SourceFile, pos: Position) -> Option<Symbol> {
    let occurrences = file_occurrences(db, file);
    occurrences.find(pos)
}
```

If file unchanged, Salsa returns cached result. If file changed but
occurrences unchanged (e.g., comment edit), symbol lookup result still
cached.

### 6. **Smart Import Invalidation** (OCaml lesson)

When a library changes:
- Check export_hash in import table
- If changed: mark current file dirty, re-elaborate on next query
- If unchanged: keep using current elaboration (early cutoff!)

This avoids cascading recompilation when library internals change but exports
don't.

---

## Implementation Phases

### Phase 1: Basic `.hwmli` with symbol table

- Serialize `Vec<Declaration>` to `.hwmli` (bincode)
- Include header, import table, export hash
- Load on import, use for downstream elaboration
- **No LSP optimizations yet**

### Phase 2: Add symbol table + occurrences

- During elaboration, collect:
  - Symbol table entry for each definition
  - Occurrence entry for each identifier
- Serialize both to `.hwmli`
- Implement hover, goto-definition using this data

### Phase 3: Type pool deduplication

- Hash-cons types during elaboration
- Store deduplicated type pool
- Symbol signatures reference type pool indices
- Reduces `.hwmli` size

### Phase 4: Lazy loading

- Split `.hwmli` into sections
- Store section offsets in header
- Load symbol table eagerly, elaboration artifacts lazily
- Use `memmap2` for large files

### Phase 5: Salsa integration

- Make `.hwmli` loading a Salsa query
- Make symbol lookup a Salsa query
- Benefit from Salsa's memoization and invalidation

### Phase 6: Per-declaration fingerprints + early cutoff

- Hash each declaration (type + value + dependencies)
- On recompilation: compare fingerprints
- Skip downstream recompilation if fingerprints match (GHC model)

---

## References

[1] Rust-analyzer architecture: https://rust-analyzer.github.io/book/contributing/architecture.html
[2] Salsa incremental computation: https://github.com/rust-analyzer/salsa
[3] GHC HIE files: https://www.haskell.org/ghc/blog/20190626-HIEFiles.html
[4] OCaml Merlin caching: https://github.com/ocaml/merlin/blob/master/doc/dev/CACHING.md
[5] Lean 4 server architecture: https://github.com/leanprover/lean4/blob/master/src/Lean/Server/README.md
[6] SemanticDB specification: https://scalameta.org/docs/semanticdb/specification.html
[7] TypeScript incremental compilation: https://typescriptlang.org/tsconfig/incremental.html
[8] Agda interface files: https://agda.readthedocs.io/en/stable/tools/interface-files.html

---

## Conclusion

For HWML, the winning combination is:

1. **Two-tier artifacts**: `.hwmli` separate from codegen output
2. **Content-addressed caching**: SHA-256 everywhere
3. **Symbol table + occurrences**: Separate data structures for metadata vs usage
4. **Type pool deduplication**: Store types once, reference by index
5. **Lazy loading**: Don't load elaboration artifacts until needed
6. **Salsa integration**: In-process memoization for LSP queries
7. **Bincode serialization**: Start simple, evolve as needed

The SemanticDB approach (separate index format, language-agnostic) is
compelling for ecosystem reasons, but for HWML's initial implementation,
a Rust-native format (bincode) with the GHC/OCaml model of caching
elaboration artifacts is the pragmatic choice. We can always add a SemanticDB
export later for third-party tool integration.
