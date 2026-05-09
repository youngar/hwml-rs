# Analysis: Compiler, Package Manager, and Build System Separation

**Date:** 2026-05-04  
**Status:** Architecture alignment analysis  
**Related:** [[decisions/ADR-004-mvs-package-manager]], [[decisions/ADR-006-multi-layer-build-configuration]], [[decisions/ADR-007-salsa-driven-compilation]], [[research/buck2-integration-patterns]], [[research/build-system-caching-synthesis]]

---

## Summary

This document analyzes how HWML's architecture aligns with the fundamental separation of concerns between **Compiler**, **Package Manager**, and **Build System** — a distinction that becomes critical when moving from monolithic tools (cargo, npm) to enterprise-grade, deterministic systems (Buck2 + Salsa + LSP).

**Key Finding:** HWML's existing ADRs already implement this separation correctly. The proposed "fetch phase" + "persistent artifacts" strategy fits perfectly into our existing architecture but clarifies some missing implementation details.

---

## The Three Responsibilities

### 1. Package Manager: Library Downloading (The Fetch Phase)

**What it does:** Resolve dependencies, download libraries, populate local cache  
**What it NEVER does:** Compile code, type-check, touch the network during builds

**Existing HWML Design:**
- **ADR-004 (MVS Package Manager):** Defines MVS resolution algorithm
- **ADR-006 Layer 1 (`hwml.toml`):** Per-library dependency declarations
- **ADR-006 Layer 3 (`hwml.lock`):** Exact resolved versions

**Missing Piece (Now Clarified):**
The **fetch phase** needs explicit implementation as a separate tool invocation:

```bash
# Phase 1: Fetch (network-touching, non-hermetic)
$ hwml fetch

# Downloads tarballs from registry
# Unpacks to ~/.hwml/registry/std-v1.4.2/
# Unpacks to ~/.hwml/registry/axi4-v2.1.0/
# Generates hwml.lock (if not exists)
# Writes path-mapping file (.hwml/resolved-deps.json)

# Phase 2: Build (hermetic, no network)
$ hwml build
# OR
$ buck2 build //lib/uart:uart
```

**Two Options for Fetch:**

**Option A: Native Buck2 Way**
```python
# In BUCK file or .bzl
http_archive(
    name = "hwml_std",
    url = "https://hwml.org/packages/std-1.4.2.tar.gz",
    sha256 = "abc123...",
)

hwml_library(
    name = "my_lib",
    deps = ["@hwml_std//:lib"],
)
```
- Buck2 handles downloading before build
- HWML compiler receives absolute paths

**Option B: `hwml fetch` Command (Hybrid)**
```bash
$ hwml fetch
# Reads hwml.toml + hwml.lock
# Downloads to ~/.hwml/registry/
# Generates .hwml/resolved-deps.json:
{
  "std": "/Users/me/.hwml/registry/std-v1.4.2",
  "axi4": "/Users/me/.hwml/registry/axi4-v2.1.0",
  "fifo": "../lib/fifo"  // Local path dep
}
```
- Buck2/LSP reads `.hwml/resolved-deps.json` to find dependencies
- Compilation phase is 100% offline

**Recommendation:** Start with **Option B** (cargo-like UX), add Option A for Buck2 power users.

---

### 2. Compiler: Pure Transformation

**What it does:** Transform source → typed IR → artifacts  
**What it NEVER does:** Download libraries, touch the network, read arbitrary files

**Existing HWML Design:**
- **ADR-007 (Salsa-Driven Compilation):** Query-based, incremental, pure functions
- **ADR-009 (rkyv Serialization):** Zero-copy `.hwmli` format

**Already Correct:**

```rust
// From ADR-007
#[salsa::tracked]
pub fn library_interface(
    db: &dyn Db,
    workspace: WorkspaceRoot,
    lib_name: String,
) -> Result<Hwmli, ElabError> {
    // ✅ GOOD: Takes explicit workspace root (Buck2 passes this)
    // ✅ GOOD: Recursively queries dependencies (pure, memoized)
    // ✅ GOOD: No network, no ambient state

    let manifest = &workspace_libraries(db, workspace)[&lib_name];

    for dep in &manifest.dependencies {
        let _dep_interface = library_interface(db, workspace, dep.name.clone())?;
    }

    elaborate_library_with_local_solver(db, workspace, lib_name)
}
```

**Compiler API (for Buck2/CLI):**
```bash
# Hermetic invocation
$ hwml-compiler \
    --workspace=/abs/path/to/workspace \
    --library=uart \
    --output=uart.hwmli \
    --dep-file=uart.d

# Compiler emits:
# - uart.hwmli (typed interface artifact)
# - uart.d (dep file listing all source files actually read)

# Compiler NEVER:
# - Downloads libraries
# - Reads ~/.hwmlconfig
# - Touches the network
# - Reads files not in workspace or dep paths
```

---

### 3. Build System: Orchestration & Caching

**What it does:** Schedule builds, deduplicate work, cache artifacts, distribute execution
**What it delegates:** Actual compilation to the compiler

**Existing HWML Design:**
- **ADR-006 Layer 2 (`hwml-build.toml`):** Build configuration (targets, caching, remote execution)
- **Research:** Buck2 integration patterns, REapi v2, CAS

**Integration Points:**

**3a. CLI Mode (Simple Projects)**
```bash
$ hwml fetch     # Download deps (once)
$ hwml build     # Compile all libraries

# Internally:
# 1. Read hwml-workspace.toml
# 2. Load .hwml/resolved-deps.json
# 3. Invoke Salsa queries
# 4. Cache .hwmli files locally (~/.hwml/cache/)
```

**3b. Buck2 Mode (Enterprise)**
```python
# BUCK file
hwml_library(
    name = "uart",
    srcs = glob(["*.hwml"]),
    deps = [
        "//lib/fifo:fifo",
        "@hwml_std//:lib",
    ],
)

# Buck2:
# 1. Calls hwml-compiler with explicit paths
# 2. Uploads .hwmli to remote cache (REapi v2)
# 3. Shares across team
```

---

## The LSP Cold-Start Problem (Solved)

### The Challenge

**Problem:** Salsa is in-memory. When VS Code restarts, all 50 libraries must re-elaborate from source.

**Bad solution:** Re-parse and type-check everything (30-60 seconds)

**Good solution:** Persistent `.hwmli` artifacts + hash-based cache invalidation

### The Solution: Persistent Build Artifacts

**Existing Design (Already in ADR-009):**
- **`.hwmli` files:** Serialized interface using rkyv (zero-copy)
- **Hash tracking:** BLAKE3 of source files
- **Early cutoff:** Only rebuild if interface changes (ADR-007)

**What Was Missing (Now Clarified):**

**LSP Boot Sequence:**

```rust
// LSP startup
fn initialize_workspace(workspace_root: PathBuf) -> HwmlDatabase {
    let db = HwmlDatabase::new();

    // Step 1: Scan workspace for libraries
    let workspace = WorkspaceRoot::new(&db, workspace_root);
    let libraries = workspace_libraries(&db, workspace);

    // Step 2: Load .hwmli artifacts from cache
    for (name, manifest) in libraries {
        let cache_path = hwmli_cache_path(&manifest);

        if let Some(cached_hwmli) = load_hwmli_if_valid(&manifest, &cache_path) {
            // ✅ CACHE HIT: Deserialize .hwmli into Salsa
            db.set_library_interface_from_cache(name, cached_hwmli);
        } else {
            // ❌ CACHE MISS: Elaborate from source (slow path)
            let interface = library_interface(&db, workspace.clone(), name)?;
            // Save for next time
            save_hwmli_to_cache(&interface, &cache_path);
        }
    }

    db
}

fn load_hwmli_if_valid(manifest: &Manifest, cache_path: &Path) -> Option<Hwmli> {
    let cached_hwmli = read_hwmli(cache_path)?;

    // Validate: Hash all source files
    let current_hash = hash_source_files(&manifest.sources);

    if cached_hwmli.source_hash == current_hash {
        Some(cached_hwmli)  // ✅ Valid cache
    } else {
        None  // ❌ Stale (source files changed)
    }
}
```

**Cache Locations:**

```
# Local cache (per-machine)
~/.hwml/cache/
├── objects/
│   ├── ab/cd/abcdef123456...  # .hwmli files (keyed by source hash)
│   └── ...
└── index.db  # SQLite: source_hash → .hwmli path

# Buck2 cache (team-wide)
# Remote CAS (REapi v2)
# Action cache: (compiler_hash + source_hash) → .hwmli
```

**LSP Performance:**

| Scenario | Without Cache | With Cache | Speedup |
|----------|---------------|------------|---------|
| **Cold start (50 libs)** | 30-60s (elaborate all) | 0.5-2s (deserialize all) | **15-120x** |
| **One file edited** | 0.5s (Salsa recomputes 1 lib) | 0.5s (same) | 1x |
| **Ten files edited** | 5s (Salsa recomputes 10 libs) | 5s (same) | 1x |

**Key Insight:** Cache doesn't help incremental edits (Salsa already handles that). Cache helps **clean boots** (after restart, after `git clean`, after switching branches).

---

## Sharing Cache Between CLI and LSP

**The Magic:** Both use the same `.hwmli` format and same cache location.

**Workflow:**

1. **Alice runs `hwml build` (CLI):**
   - Elaborates `fifo` library
   - Saves `fifo.hwmli` to `~/.hwml/cache/`
   - Buck2 uploads to remote cache

2. **Bob pulls main and opens VS Code (LSP):**
   - LSP checks local cache: `fifo.hwmli` exists, hash matches
   - **Instant load** (deserialize, no elaboration)

3. **Bob runs `buck2 build` (first time):**
   - Buck2 checks remote cache
   - Downloads `fifo.hwmli` (built by Alice)
   - **Instant build** (no compilation)

**Cache Key:**
```rust
struct CacheKey {
    source_hash: Blake3Hash,      // Hash of all .hwml source files
    compiler_version: String,     // "hwml-0.3.0"
    config_hash: Blake3Hash,      // Hash of features, flags
}

// Lookup:
let key = CacheKey {
    source_hash: blake3::hash(concat_files(&["fifo.hwml", "impl.hwml"])),
    compiler_version: "hwml-0.3.0",
    config_hash: blake3::hash(features),
};

if let Some(hwmli) = cache.get(key) {
    return hwmli;  // Cache hit!
}
```

---

## How This Fits Into Existing Architecture

### ADR-004 (MVS Package Manager) — ✅ No Changes Needed

**What it does:** Define MVS algorithm, version resolution

**Clarification:**
- MVS runs during **fetch phase** (`hwml fetch`)
- Generates `hwml.lock` with exact versions
- Compiler **never** runs MVS (it just reads `hwml.lock`)

### ADR-006 (Multi-Layer Build Configuration) — ✅ Minor Additions

**What it does:** Define `hwml.toml`, `hwml-build.toml`, `hwml.lock`

**Additions Needed:**

**Section to add to ADR-006:**

```markdown
## Library Fetching and Resolution

### The Fetch Phase

Before any compilation can occur, external dependencies must be downloaded and made available locally. This is handled by the `hwml fetch` command:

**Fetch algorithm:**
1. Read `hwml.toml` (all libraries in workspace)
2. Read `hwml.lock` (if exists); otherwise run MVS solver (ADR-004)
3. For each external dependency:
   - Check local cache: `~/.hwml/registry/<name>-v<version>/`
   - If missing: Download tarball from registry
   - Verify checksum (from `hwml.lock`)
   - Unpack to cache
4. Generate `.hwml/resolved-deps.json` (path mapping for compilation)

**Resolved dependencies file (`.hwml/resolved-deps.json`):**
```json
{
  "std": "/Users/me/.hwml/registry/std-v1.4.2",
  "axi4": "/Users/me/.hwml/registry/axi4-v2.1.0",
  "fifo": "../lib/fifo"  // Local path dep
}
```

**Usage:**
- CLI: `hwml fetch` before `hwml build`
- Buck2: `http_archive` rules download before build
- LSP: Reads `.hwml/resolved-deps.json` on startup

**Important:** The compiler NEVER downloads libraries. It only reads the resolved paths.
```

### ADR-007 (Salsa-Driven Compilation) — ✅ Minor Additions

**What it does:** Define Salsa query architecture

**Additions Needed:**

**Section to add to ADR-007:**

```markdown
## Persistent Artifact Caching for LSP

To avoid re-elaborating all libraries on LSP startup, we serialize `.hwmli` artifacts to disk.

**Cache structure:**
```
~/.hwml/cache/
├── objects/ab/cd/abcdef123456...  # .hwmli files
└── index.db  # SQLite: source_hash → path
```

**LSP boot sequence:**
```rust
for (name, manifest) in workspace_libraries(&db, workspace) {
    if let Some(cached) = load_hwmli_if_valid(&manifest) {
        db.set_library_interface_from_cache(name, cached);  // Instant
    } else {
        library_interface(&db, workspace, name)?;  // Slow (elaborate)
    }
}
```

**Cache validation:**
- Hash all source files: `BLAKE3(concat(fifo.hwml, impl.hwml))`
- Compare with `cached_hwmli.source_hash`
- If match → use cache
- If mismatch → re-elaborate

**Sharing with Buck2:**
- CLI builds write `.hwmli` to local cache
- Buck2 uploads to remote cache (REapi v2)
- LSP can fetch from remote if local miss
```

---

## Implementation Roadmap

### Phase 1: Local Fetch + Local Cache (MVP)

**Goal:** cargo-like experience without Buck2

**Components:**
1. **`hwml fetch` command**
   - Implement MVS solver (ADR-004 algorithm)
   - Download tarballs from registry
   - Unpack to `~/.hwml/registry/`
   - Generate `hwml.lock` and `.hwml/resolved-deps.json`

2. **Local `.hwmli` cache**
   - Implement rkyv serialization (ADR-009)
   - Save to `~/.hwml/cache/objects/`
   - SQLite index for lookups

3. **LSP persistent loading**
   - Check cache on startup
   - Deserialize `.hwmli` → Salsa inputs
   - Fall back to elaboration on cache miss

**Success Metrics:**
- `hwml fetch` downloads ~50 std libraries in <10s
- LSP cold start: 50 libraries in <2s (vs 30s without cache)
- `hwml build` after `git clean`: <5s (all from cache)

---

### Phase 2: Remote Cache (Buck2 Integration)

**Goal:** Team-wide caching via REapi v2

**Components:**
1. **Remote CAS client**
   - REapi v2 gRPC client
   - Upload `.hwmli` after compilation
   - Download on cache miss

2. **Buck2 rules**
   - `hwml_library()` rule
   - Calls `hwml-compiler` with explicit paths
   - Integrates with Buck2's action cache

3. **Fetch integration**
   - Buck2 can call `hwml fetch` as a genrule
   - OR use `http_archive` for external deps

**Success Metrics:**
- Remote cache hit rate: >90% on CI
- Build time (with cache): <1min for 100+ libraries
- Cache shared across Alice, Bob, CI

---

### Phase 3: Persistent Worker Protocol

**Goal:** Sub-second LSP responsiveness with Buck2 hermeticity

**Components:**
1. **Long-running daemon**
   - Persistent Salsa database in memory
   - Listens on Unix socket
   - Buck2 sends compilation requests

2. **Incremental state**
   - Daemon keeps Salsa memoization across builds
   - File change → Salsa recomputes only affected
   - Result: 2ms rebuild for 1-line change

**Success Metrics:**
- Incremental build: <10ms for 1-file change
- Memory usage: <2GB for 100-library workspace
- Hermeticity: Still works with `--no-remote-cache`

---

## Answers to Original Questions

### Q: "How to download libraries without violating hermetic builds?"

**A:** Separate **fetch phase** (network-touching, generates `.hwml/resolved-deps.json`) from **build phase** (hermetic, reads paths from file).

- Option A: Buck2 `http_archive` (Buck2-native)
- Option B: `hwml fetch` command (cargo-like UX)

**Recommendation:** Start with Option B, add Option A for Buck2 users.

---

### Q: "How to solve LSP cold-start without violating Salsa architecture?"

**A:** Persistent `.hwmli` artifacts cached on disk, validated by source hash.

- Cache location: `~/.hwml/cache/`
- Cache key: `BLAKE3(source files) + compiler_version`
- LSP deserializes cache into Salsa inputs (not bypassing Salsa, feeding it)

**Benefit:** 15-120x faster cold start (0.5s vs 30s for 50 libraries).

---

### Q: "How to share cache between CLI and LSP?"

**A:** Both write to same cache directory.

- CLI builds → writes `.hwmli` to cache
- LSP boots → reads `.hwmli` from cache
- Buck2 uploads → remote cache → other developers download

**Result:** Alice's CLI build speeds up Bob's LSP.

---

### Q: "Will libraries be hosted as Git repos or tarballs?"

**Proposal:** **Both**, with tarballs as primary.

**Registry structure:**
```
https://hwml.org/packages/
├── std-1.4.2.tar.gz
├── axi4-2.1.0.tar.gz
└── index.json  # Package metadata

# Tarball contents:
std-1.4.2/
├── hwml.toml
├── src/
│   ├── vec.hwml
│   ├── option.hwml
│   └── ...
└── README.md
```

**Git fallback:**
```toml
[dependencies]
experimental-lib = { git = "https://github.com/user/lib.git", tag = "v0.1.0" }
```

**Rationale:**
- Tarballs: Fast, immutable, easy to cache, checksum verification
- Git: Development, pre-release, forks, local changes

---

## Summary

**Your proposal is 100% correct and fits perfectly into our existing architecture.**

The key clarifications this analysis provides:

1. **Fetch Phase:** Explicitly separate `hwml fetch` (downloads libraries) from `hwml build` (compilation)

2. **Persistent Artifacts:** `.hwmli` files ARE the cache format (already in ADR-009)

3. **LSP Boot:** Deserialize `.hwmli` into Salsa inputs (not bypassing Salsa)

4. **Cache Sharing:** CLI, LSP, Buck2 all write to same cache (REapi v2 for remote)

**No major architecture changes needed.** Just:
- Add `hwml fetch` implementation
- Add cache serialization/deserialization to LSP
- Document the separation clearly (this analysis document)

**Next Steps:**
1. Add "Fetch Phase" section to ADR-006
2. Add "Persistent Caching" section to ADR-007
3. Implement `hwml fetch` (Phase 1)
