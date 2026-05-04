# Build System Caching and Databases: Synthesis and Recommendations for HWML

**Date:** 2026-05-03  
**Status:** Complete  
**Related:** [[research/content-addressable-storage-systems]], [[research/incremental-compilation-synthesis]], [[research/modern-build-systems]], [[decisions/ADR-006-multi-layer-build-configuration]]

---

## Executive Summary

This document synthesizes research on caching systems, persistent stores, and databases used in modern build systems (Buck2, Bazel, Nix, Shake, Ninja) and academic work on incremental computation. It provides concrete recommendations for HWML's build system architecture.

**Key findings:**
1. **CAS is fundamental**: All modern build systems use content-addressable storage
2. **Hybrid is optimal**: In-process (Salsa/DICE) + persistent (CAS) provides best performance
3. **BLAKE3 is the future**: 10x faster than SHA-256, widely adopted for new systems
4. **Early cutoff is critical**: Detect unchanged outputs to skip downstream rebuilds
5. **Three-tier caching**: Local + user-global + remote for maximum efficiency

---

## 1. The Landscape: How Modern Build Systems Cache

### Comparison Matrix

| System | In-Process Cache | Persistent DB | Remote Cache | Hash Function | Early Cutoff |
|--------|-----------------|---------------|--------------|---------------|--------------|
| **Make** | None | Mtimes only | None | None | ❌ No |
| **Ninja** | Task graph | `.ninja_deps` (binary) | None | Command hash (SHA-1) | ❌ No |
| **Shake** | Haskell maps | `.shake.database` | Experimental | Configurable | ✅ Yes |
| **Bazel** | Skyframe (in-mem) | None (rebuilds graph) | REapi v2 (SHA-256) | SHA-256 | ✅ Yes |
| **Buck2** | DICE (in-mem) | None (rebuilds graph) | REapi v2 (SHA-256) | SHA-256 | ✅ Yes |
| **Nix** | None | `/nix/store` paths | Binary cache (HTTP) | SHA-256 | ⚠️ Partial (CA only) |
| **Salsa** | Memoization tables | None | None | Rust type equality | ✅ Yes |

### Architecture Patterns

**Pattern 1: Static Graph + Mtime (Make, traditional)**
```
Read Makefile → Build dependency DAG → Check mtimes → Execute outdated
```
- **Pro**: Simple, fast startup
- **Con**: No remote caching, false rebuilds (mtime != content), no early cutoff

**Pattern 2: Dynamic Graph + Persistent Store (Shake)**
```
Load database → Execute rules (discover dependencies) → Store traces → Verify on next run
```
- **Pro**: Flexible (Haskell DSL), supports dynamic deps, cloud caching (experimental)
- **Con**: Haskell ecosystem, persistent DB can grow large

**Pattern 3: In-Memory + Remote CAS (Buck2, Bazel)**
```
Build graph in memory → Check remote cache → Execute locally/remotely → Upload to cache
```
- **Pro**: Fast, scalable, remote execution, early cutoff
- **Con**: Graph rebuild on every invocation (mitigated by caching)

**Pattern 4: Persistent Functional Store (Nix)**
```
Eval derivations → Check binary cache → Build derivation → Store in /nix/store
```
- **Pro**: Hermetic, reproducible, content-addressed (with RFC 0062)
- **Con**: Slow (no in-process cache), large disk usage, CA experimental

**For HWML: Pattern 3 + Salsa**
- **Salsa** for in-process incremental elaboration (like rust-analyzer)
- **CAS** for persistent `.hwmli` caching (like Buck2)
- **REapi v2** for remote cache (compatible with existing infrastructure)

---

## 2. Content-Addressable Storage: Core Techniques

### Hashing Strategy

**Why BLAKE3:**
| Metric | SHA-256 | BLAKE2b | BLAKE3 |
|--------|---------|---------|--------|
| **Speed** | 1.5 GB/s | 3 GB/s | **10 GB/s** |
| **Parallelism** | ❌ Serial | ⚠️ Limited | ✅ Full |
| **Security** | ✅ Strong | ✅ Strong | ✅ Strong |
| **Adoption** | Universal | Growing | **Emerging** |

**BLAKE3 advantages for build systems:**
1. **Performance**: Hash 10GB artifact in 1 second (vs 7 seconds for SHA-256)
2. **Incremental**: Efficiently update hash as data streams in
3. **Parallel**: Can hash across multiple cores
4. **Tree mode**: Merkle tree structure for range proofs
5. **Standardized**: Rust crate + C reference implementation

**Deployment strategy:**
- Primary: BLAKE3 for all new artifacts
- Compatibility: Support SHA-256 for interop with Bazel/Buck2 REapi
- Migration: Convert SHA-256 → BLAKE3 gradually (both in database)

### Storage Sharding

**Problem:** Millions of artifacts → filesystem bottleneck (too many files in one directory)

**Solution:** Shard by hash prefix (Git-style)
```
~/.cache/hwml/cas/
  ab/cdef123456789...  ← first 2 hex chars = directory
  ab/cdef987654321...
  cd/1234567890abc...
```

**Why 2 hex chars (256 directories)?**
- 1 hex char: 16 dirs → still too many files per dir
- 2 hex chars: 256 dirs → ~4000 files/dir for 1M artifacts ✅
- 3 hex chars: 4096 dirs → overhead of creating directories

**Alternative:** Database (SQLite, RocksDB)
- **Pro**: No filesystem limits, atomic operations, easier queries
- **Con**: Slower for large blobs, one point of failure
- **Verdict**: Filesystem for blobs, SQLite for metadata (if needed)

### Hardlinking for Zero-Copy

**Technique:**
```rust
// Instead of copying
fs::copy(cas_path, build_path)?;  // 1 GB file → 1 GB copied

// Use hardlink
fs::hard_link(cas_path, build_path)?;  // 1 GB file → 0 bytes copied, instant
```

**Requirements:**
- Same filesystem (can't hardlink across `/` and `/home`)
- Artifact must be immutable (never modify hardlinked files!)

**Fallback:**
- If hardlink fails (cross-filesystem), copy
- If copy fails (permission), symlink (less safe)

**For HWML:**
```rust
fn materialize_from_cas(hash: Blake3Hash, dest: &Path) -> Result<()> {
    let cas_path = cas_dir().join(hash.shard_path());
    
    // Try hardlink first
    if fs::hard_link(&cas_path, dest).is_ok() {
        return Ok(());
    }
    
    // Fall back to copy
    fs::copy(&cas_path, dest)?;
    Ok(())
}
```

---

## 3. Early Cutoff: The Critical Optimization

### What is Early Cutoff?

**Without early cutoff:**
```
Source file changes → Recompile → New .o file (identical bytes) → Relink (unnecessary)
```

**With early cutoff:**
```
Source file changes → Recompile → New .o file
  ↓ compare hash
Old hash == New hash? YES → Skip downstream (linker not re-run)
```

**Impact:** Can reduce rebuilds by 10-100x for typical edits

### GHC's Implementation (Best Practice)

**Per-declaration fingerprints:**
```haskell
-- Module A exports:
data Foo = Foo Int
func :: Foo -> String

-- Fingerprints stored in .hi file:
data_Foo_fingerprint = hash("data Foo = Foo Int")
func_fingerprint = hash("func :: Foo -> String")
```

**Usage tracking:**
```haskell
-- Module B imports A:
import A (Foo, func)  -- uses func

-- B's .hi file records:
depends_on_A = [func_fingerprint]
-- (does NOT depend on data_Foo_fingerprint)
```

**Rebuild decision:**
```haskell
-- A changes: add new function (doesn't affect Foo or func)
-- A's data_Foo_fingerprint: unchanged
-- A's func_fingerprint: unchanged
-- B's rebuild check: all used fingerprints unchanged → SKIP ✅
```

### HWML Application

**`.hwmli` structure:**
```rust
pub struct Hwmli {
    pub library_name: String,
    pub declarations: Vec<Declaration>,
    pub export_interface_hash: Blake3Hash,  // hash of public interface
    pub declaration_fingerprints: HashMap<DeclId, Blake3Hash>,
    pub usage_map: HashMap<LibraryName, Vec<DeclId>>,  // which decls we used
}
```

**Elaboration with tracking:**
```rust
fn elaborate_library(db: &dyn Db, lib: Library) -> Result<Hwmli> {
    let mut usage_tracker = UsageTracker::new();
    
    for decl in lib.declarations() {
        // During elaboration, track which imported decls we consult
        let result = elaborate_decl(db, decl, &mut usage_tracker)?;
        // ...
    }
    
    // Store usage information in .hwmli
    Hwmli {
        usage_map: usage_tracker.finalize(),
        // ...
    }
}
```

**Rebuild decision:**
```rust
fn needs_rebuild(lib: Library, old_hwmli: &Hwmli) -> bool {
    for (dep_lib, used_decls) in &old_hwmli.usage_map {
        let current_hwmli = load_hwmli(dep_lib);
        for decl_id in used_decls {
            let old_fingerprint = current_hwmli.declaration_fingerprints[decl_id];
            let new_fingerprint = compute_fingerprint(dep_lib, decl_id);
            if old_fingerprint != new_fingerprint {
                return true;  // Dependency changed, must rebuild
            }
        }
    }
    false  // All dependencies unchanged, can reuse!
}
```

---

## 4. Three-Tier Caching Architecture

### Tier 1: Local Build Directory

**Path:** `.hwml-build/`  
**Purpose:** Working directory for current build  
**Lifetime:** Disposable (removed by `hwml clean`)

**Structure:**
```
.hwml-build/
  uart-controller-abc123.hwmli  ← hardlink to Tier 2
  fifo-def456.hwmli
  build.log
  .lock  ← prevent concurrent builds
```

**Performance:**
- Fast access (local disk, probably SSD)
- Hardlinked from Tier 2 (zero-copy)
- Small (only current build's artifacts)

### Tier 2: User-Global CAS

**Path:** `~/.cache/hwml/cas/`  
**Purpose:** Share artifacts across projects on one machine  
**Lifetime:** Persistent, GC'd when over size limit

**Structure:**
```
~/.cache/hwml/cas/
  ab/cdef123456...  ← BLAKE3 hash, sharded
  metadata.db  ← SQLite (optional): access times, refcounts
```

**Garbage Collection:**
```rust
struct CasEntry {
    hash: Blake3Hash,
    size: u64,
    last_access: SystemTime,
    ref_count: u32,  // how many Tier 1 hardlinks?
}

fn gc_if_needed() {
    if total_size() < config.max_cache_size {
        return;  // Under limit
    }
    
    // Sort by: refcount (0 first), then last_access (oldest first)
    let mut entries = list_all_entries();
    entries.sort_by_key(|e| (e.ref_count, e.last_access));
    
    // Evict until under limit (leave 10% headroom)
    let target = config.max_cache_size * 0.9;
    while total_size() > target {
        let entry = entries.pop_front();
        if entry.ref_count == 0 {  // Safe to delete
            delete_entry(entry.hash);
        }
    }
}
```

### Tier 3: Remote Shared Cache

**Protocol:** Bazel Remote Execution API v2  
**Servers:** BuildBuddy, Buildbarn, Google RBE  
**Purpose:** Share across team, CI, time

**Read flow:**
```
Check Tier 1 → miss
  ↓
Check Tier 2 → miss
  ↓
Check Tier 3 (remote)
  ↓ HTTP GET /cas/{hash}
Download to Tier 2
  ↓
Hardlink to Tier 1
```

**Write flow:**
```
Build artifact
  ↓
Store in Tier 1
  ↓
Copy to Tier 2 (or hardlink if possible)
  ↓
Upload to Tier 3 (async, best-effort)
```

**Access control:**
- **Read**: Open to all developers (speeds up local builds)
- **Write**: Restricted to CI only (ensures hermetic builds)

**Why CI-only writes?**
- Local builds might not be hermetic (modified files, wrong env vars)
- CI builds are controlled, reproducible
- Prevents cache poisoning

**Configuration:**
```toml
# In hwml-build.toml
[cache]
local = ".hwml-build"
user_global = "~/.cache/hwml/cas"
user_global_max_size_gb = 10

[cache.remote]
url = "https://cache.company.com"
read_auth = "token_from_env"  # Optional: read auth
write_auth = "ci_only_token"  # Env var only set in CI
```

---

## 5. In-Process Incremental Computation: Salsa

### Why Salsa for HWML?

**Use case:** Fast LSP + incremental `hwml build`

**Scenario:**
```
User edits uart.hwml → Type-check → LSP shows errors (<100ms)
User runs `hwml build` → Reuse LSP's elaboration → Fast build
```

**Without Salsa:**
- LSP elaborates uart.hwml
- User runs `hwml build`
- Build elaborates uart.hwml again (duplicate work!)

**With Salsa:**
- LSP and CLI share same `Database`
- Elaboration results memoized in Salsa
- LSP elaborates uart.hwml → stored in DB
- User runs `hwml build` → Salsa cache hit → Instant!

### Salsa Architecture for HWML

**Database trait:**
```rust
#[salsa::db]
trait Db: salsa::Database {
    // Inputs
    fn workspace(&self) -> Workspace;
    fn source_file(&self, path: PathBuf) -> SourceFile;

    // Tracked functions (derived queries)
    fn parse_file(&self, source: SourceFile) -> SurfaceProgram;
    fn elaborate_library(&self, lib: Library) -> Hwmli;
}
```

**Memoization example:**
```rust
#[salsa::tracked]
fn elaborate_library(db: &dyn Db, lib: Library) -> Hwmli {
    // This function is memoized by Salsa
    // If called again with same lib (and dependencies unchanged), return cached result

    let deps = lib.dependencies(db);
    for dep in deps {
        // Salsa tracks that we called elaborate_library(dep)
        let dep_hwmli = elaborate_library(db, dep);
        // ...
    }

    // Elaborate this library
    let decls = elaborate_all_declarations(db, lib);
    Hwmli { declarations: decls, /* ... */ }
}
```

**Incremental re-elaboration:**
```rust
// Edit source file
db.set_source_file(path, new_content);

// Salsa automatically:
// 1. Marks parse_file(old_source) as stale
// 2. Marks elaborate_library(lib) as potentially stale
// 3. Re-runs only if dependencies actually changed
let hwmli = elaborate_library(db, lib);  // Might reuse cache!
```

### Durability for Standard Libraries

**Problem:** Editing project file invalidates std library queries

**Solution:** Durability levels
```rust
db.set_source_file_with_durability(
    std_lib_path,
    content,
    salsa::Durability::HIGH  // Changes rarely
);

db.set_source_file_with_durability(
    project_path,
    content,
    salsa::Durability::LOW  // Changes frequently
);
```

**Version vector:**
```
[low_durability_version, high_durability_version]
```

- Editing project file increments `low_durability_version`
- Queries depending on std lib check `high_durability_version` (unchanged!)
- Result: Editing project doesn't invalidate std lib

---

## 6. Persistent Memoization: Bridging Salsa and CAS

### The Gap

**Salsa:** In-memory, lost on process exit
**CAS:** On-disk, survives across invocations

**Problem:** LSP process and CLI process don't share memory

**Solution 1: Shared Memory (complex)**
- LSP writes Salsa DB to shared memory
- CLI reads from shared memory
- **Con**: Platform-specific, complex lifecycle

**Solution 2: Serialize Salsa (experimental)**
- Salsa doesn't natively support serialization
- Would need custom implementation
- **Con**: Large serialized size, slow

**Solution 3: Hybrid (recommended)**
- Salsa for in-process (LSP, single build)
- CAS for cross-process (CLI builds, remote cache)
- Accept some duplication

### Workflow

**LSP (long-lived process):**
```rust
struct LspDatabase {
    salsa_storage: salsa::Storage<Self>,
}

impl LspDatabase {
    fn on_file_change(&mut self, path: PathBuf, content: String) {
        self.set_source_file(path, content);
        // Salsa incrementally re-elaborates
    }

    fn diagnostics(&self, path: PathBuf) -> Vec<Diagnostic> {
        let lib = self.library_for_file(path);
        let hwmli = self.elaborate_library(lib);  // Salsa memoized
        extract_diagnostics(hwmli)
    }
}
```

**CLI (short-lived process):**
```rust
fn main() {
    let mut db = CliDatabase::new();
    let workspace = Workspace::load(".")?;
    db.set_workspace(workspace);

    for lib in workspace.topo_order() {
        // Check CAS first
        let hash = compute_input_hash(&lib);
        if let Some(hwmli) = load_from_cas(hash) {
            // Cache hit! Skip elaboration
            continue;
        }

        // Cache miss: elaborate (Salsa memoized within this build)
        let hwmli = db.elaborate_library(lib);

        // Store in CAS for next invocation
        store_in_cas(hash, &hwmli);
    }
}
```

**Best of both worlds:**
- LSP: Fast incremental updates (Salsa)
- CLI: Fast across builds (CAS)
- Minimal duplication (acceptable trade-off)

---

## 7. Remote Execution: REapi v2 Integration

### Why Remote Execution?

**Benefits:**
1. **Parallelism**: Execute 1000s of actions concurrently
2. **Fast machines**: Cloud executors with 64+ cores
3. **Shared cache**: All developers benefit from each other's builds
4. **CI efficiency**: Reuse local dev builds in CI

**For HWML:**
- Elaborating 100 libraries sequentially: slow
- Elaborating 100 libraries in parallel remotely: fast!

### REapi v2 Protocol

**Key operations:**
```protobuf
service Execution {
  rpc Execute(ExecuteRequest) returns (stream ExecuteResponse);
}

service ActionCache {
  rpc GetActionResult(GetActionResultRequest) returns (ActionResult);
  rpc UpdateActionResult(UpdateActionResultRequest) returns (ActionResult);
}

service ContentAddressableStorage {
  rpc FindMissingBlobs(FindMissingBlobsRequest) returns (FindMissingBlobsResponse);
  rpc BatchUpdateBlobs(BatchUpdateBlobsRequest) returns (BatchUpdateBlobsResponse);
  rpc BatchReadBlobs(BatchReadBlobsRequest) returns (BatchReadBlobsResponse);
}
```

**Execution flow:**
```
1. Client computes Action hash
2. Client checks ActionCache (cache hit?)
   ↓ miss
3. Client uploads inputs to CAS (only missing blobs)
4. Client calls Execute(Action)
5. Server checks ActionCache again (race condition protection)
   ↓ miss
6. Server downloads inputs from CAS
7. Server executes action in sandbox
8. Server uploads outputs to CAS
9. Server stores ActionResult in ActionCache
10. Client downloads outputs from CAS
```

### HWML Action Example

**Action:**
```json
{
  "command_digest": "sha256:abc123...",
  "input_root_digest": "sha256:def456...",
  "timeout": "300s",
  "platform": {
    "properties": [
      {"name": "OSFamily", "value": "Linux"},
      {"name": "container-image", "value": "docker://hwml-builder:0.3.0"}
    ]
  }
}
```

**Command:**
```json
{
  "arguments": [
    "hwml-elaborate",
    "--library", "uart-controller",
    "--output", "uart-controller.hwmli"
  ],
  "environment_variables": [
    {"name": "HWML_VERSION", "value": "0.3.0"}
  ],
  "output_files": ["uart-controller.hwmli"]
}
```

**Input root (Directory):**
```json
{
  "files": [
    {"name": "uart.hwml", "digest": "sha256:111..."},
    {"name": "fifo.hwml", "digest": "sha256:222..."}
  ],
  "directories": [
    {"name": "deps", "digest": "sha256:333..."}
  ]
}
```

**Implementation:**
```rust
async fn execute_remote(action: Action) -> Result<Hwmli> {
    let client = ReapiClient::connect(remote_url).await?;

    // 1. Check action cache
    if let Some(result) = client.get_action_result(action.hash()).await? {
        return download_hwmli(result.output_digest).await;
    }

    // 2. Find missing blobs
    let all_blobs = collect_input_blobs(&action);
    let missing = client.find_missing_blobs(all_blobs).await?;

    // 3. Upload missing blobs
    client.batch_update_blobs(missing).await?;

    // 4. Execute action
    let response = client.execute(action).await?;

    // 5. Download output
    download_hwmli(response.output_digest).await
}
```

---

## 8. Recommendations for HWML

### Phase 1: Local CAS (Months 1-2)

**Deliverables:**
- BLAKE3 hashing for `.hwmli` files
- Tier 1 (build dir) + Tier 2 (user-global CAS)
- Hardlinking for zero-copy
- Basic GC (LRU with size limit)

**Implementation:**
```rust
// crates/hwml-cas/src/lib.rs
pub struct ContentAddressableStore {
    root: PathBuf,  // ~/.cache/hwml/cas
    max_size: u64,
}

impl ContentAddressableStore {
    pub fn store(&self, content: &[u8]) -> Result<Blake3Hash> {
        let hash = blake3::hash(content);
        let path = self.blob_path(&hash);
        fs::create_dir_all(path.parent().unwrap())?;
        fs::write(&path, content)?;
        Ok(hash)
    }

    pub fn load(&self, hash: &Blake3Hash) -> Result<Vec<u8>> {
        let path = self.blob_path(hash);
        fs::read(&path)
    }

    fn blob_path(&self, hash: &Blake3Hash) -> PathBuf {
        let hex = hash.to_hex();
        self.root.join(&hex[0..2]).join(&hex[2..])
    }
}
```

**Success metrics:**
- Cache hit rate >50% on incremental builds
- Hardlink success rate >90% (same filesystem)
- GC keeps cache under limit

### Phase 2: Salsa Integration (Months 2-3)

**Deliverables:**
- Salsa database for elaboration
- Tracked functions for parsing, elaboration
- LSP integration (share DB)
- Durability for std library

**Implementation:**
```rust
// crates/hwml-db/src/lib.rs
#[salsa::db]
pub trait Db: salsa::Database {
    #[salsa::input]
    fn workspace(&self) -> Workspace;

    #[salsa::input]
    fn source_file(&self, id: SourceFileId) -> SourceFile;
}

#[salsa::tracked]
pub fn parse_file(db: &dyn Db, source: SourceFile) -> SurfaceProgram {
    // Parser logic
}

#[salsa::tracked]
pub fn elaborate_library(db: &dyn Db, lib: Library) -> Hwmli {
    // Elaboration logic
}
```

**Success metrics:**
- LSP diagnostics <100ms for typical edits
- Incremental build reuses >80% of Salsa cache
- Durability prevents std lib invalidation

### Phase 3: Early Cutoff (Months 4-5)

**Deliverables:**
- Per-declaration fingerprints in `.hwmli`
- Usage tracking during elaboration
- Rebuild logic checks fingerprints
- GHC-style recompilation avoidance

**`.hwmli` format:**
```rust
pub struct Hwmli {
    pub version: u32,
    pub library_name: String,
    pub export_interface_hash: Blake3Hash,

    // Early cutoff support
    pub declarations: Vec<Declaration>,
    pub declaration_fingerprints: HashMap<DeclId, Blake3Hash>,
    pub usage_map: HashMap<LibraryName, HashSet<DeclId>>,
}
```

**Success metrics:**
- >90% of unchanged downstream libraries skipped
- Fingerprint computation <5% of elaboration time
- Usage tracking overhead <10%

### Phase 4: Remote Cache (Months 6-7)

**Deliverables:**
- REapi v2 client (gRPC)
- Upload on build (async, best-effort)
- Download on cache miss
- Integration with BuildBuddy/Buildbarn

**Configuration:**
```toml
[cache.remote]
url = "grpcs://buildbuddy.example.com"
instance_name = "hwml-project"
read_auth_env = "BUILDBUDDY_API_KEY"
write_auth_env = "CI_BUILDBUDDY_WRITE_KEY"
```

**Success metrics:**
- CI cache hit rate >70%
- Remote cache reduces clean build time by >50%
- Upload/download overhead <10% of build time

### Phase 5: Remote Execution (Months 8-10)

**Deliverables:**
- REapi v2 execution client
- Hermetic elaboration actions
- Container image with hwml compiler
- Parallel remote elaboration

**Success metrics:**
- 10x parallelism over local builds (100 actions → 10s instead of 100s)
- Remote execution overhead <20% per action
- Cache hit rate on remote executors >60%

---

## 9. Summary: The Complete Picture

**HWML's caching architecture:**

```
┌─────────────────────────────────────────────────────────────┐
│                                                             │
│  Developer Workstation                                      │
│                                                             │
│  ┌──────────────┐         ┌───────────────┐               │
│  │   LSP Server │────────>│ Salsa Database│               │
│  └──────────────┘         └───────────────┘               │
│         │                        │                         │
│         v                        v                         │
│  ┌──────────────┐         ┌───────────────┐               │
│  │  CLI (hwml)  │────────>│  Tier 1 Cache │               │
│  └──────────────┘         │  .hwml-build/ │               │
│         │                 └───────────────┘               │
│         │                        │ hardlink               │
│         v                        v                         │
│  ┌────────────────────────────────────────┐               │
│  │         Tier 2 Cache (CAS)             │               │
│  │      ~/.cache/hwml/cas/ (BLAKE3)       │               │
│  └────────────────────────────────────────┘               │
│                    │                                       │
└────────────────────┼───────────────────────────────────────┘
                     │
                     v  REapi v2 (gRPC)
          ┌──────────────────────────┐
          │   Tier 3: Remote Cache   │
          │                          │
          │  BuildBuddy / Buildbarn  │
          │    (SHA-256 + BLAKE3)    │
          └──────────────────────────┘
                     │
                     v
          ┌──────────────────────────┐
          │   Remote Executors       │
          │                          │
          │   Parallel elaboration   │
          │   (1000s of machines)    │
          └──────────────────────────┘
```

**Key properties:**
1. **Salsa**: In-process, <100ms LSP response
2. **Tier 1**: Fast local access, disposable
3. **Tier 2**: Zero-copy hardlinks, user-global sharing
4. **Tier 3**: Team-wide sharing, CI acceleration
5. **Remote exec**: Massive parallelism, cloud scale
6. **Early cutoff**: Skip 90% of rebuilds
7. **BLAKE3**: 10x faster hashing

---

## References

**Systems:**
- Buck2 DICE: https://github.com/facebook/buck2/tree/main/dice
- Bazel REapi: https://github.com/bazelbuild/remote-apis
- Salsa: https://github.com/salsa-rs/salsa
- Nix RFC 0062: https://github.com/NixOS/rfcs/blob/master/rfcs/0062-content-addressed-paths.md

**Papers:**
- Mokhov et al., "Build Systems à la Carte", ICFP 2018
- Erdweg et al., "A Sound and Optimal Incremental Build System with Dynamic Dependencies", OOPSLA 2015
- Mitchell, "Shake Before Building", ICFP 2012

**Tools:**
- BLAKE3: https://github.com/BLAKE3-team/BLAKE3
- BuildBuddy: https://www.buildbuddy.io/
- Buildbarn: https://github.com/buildbarn/

---

**Next Actions:**
1. Prototype BLAKE3 integration in `hwml-cas` crate
2. Design `.hwmli` serialization format (with fingerprints)
3. Integrate Salsa into `hwml-db` crate
4. Measure baseline: elaboration time, artifact sizes
5. Implement Tier 1 + Tier 2 caching
6. Benchmark cache hit rates on real hardware projects
