# Content-Addressable Storage Systems for Build Systems

**Date:** 2026-05-03  
**Status:** Research complete  
**Related:** [[research/modern-build-systems]], [[research/incremental-compilation-synthesis]], [[decisions/ADR-006-multi-layer-build-configuration]]

---

## Executive Summary

Content-addressable storage (CAS) is a fundamental technique where data is identified by the cryptographic hash of its contents rather than by location or name. This property enables:

- **Deduplication**: Identical content stored once, referenced many times
- **Verification**: Content integrity verified by recomputing hash
- **Distribution**: Content can be fetched from any source that provides matching hash
- **Early cutoff**: Detect when outputs haven't actually changed despite input changes

Modern build systems (Buck2, Bazel, Nix) use CAS for artifact caching, remote execution, and cross-user/cross-clone deduplication.

---

## 1. Core CAS Principles

### Content-Addressing vs Input-Addressing

**Input-addressed (traditional)**:
```
output_path = hash(derivation_inputs + build_script + dependencies)
```
- Path determined before building
- Change to any input → new output path
- Forces rebuilds even if output is identical

**Content-addressed**:
```
output_path = hash(output_contents)
```
- Path determined after building
- Identical outputs → same path (deduplication)
- Enables early cutoff (skip downstream if output unchanged)

### Merkle DAGs (Directed Acyclic Graphs)

CAS systems organize data as Merkle DAGs:
```
Directory A (hash: abc123)
├── file1.txt (hash: def456)
├── file2.txt (hash: def456)  ← same content, same hash
└── subdir B (hash: 789abc)
    └── file3.txt (hash: ghi789)
```

**Properties:**
- Each node identified by hash of its content
- Directories hash their children's hashes
- Shared content deduplicated automatically
- Tamper-evident (any change propagates to root hash)

---

## 2. CAS in Modern Build Systems

### Git's Object Store

**Data model:**
- Blobs: file contents
- Trees: directory listings (name → hash mappings)
- Commits: metadata + tree hash
- All stored in `.git/objects/`

**Storage strategy:**
```
.git/objects/ab/cdef123456...  (first 2 hex chars = directory)
```

**Key insights:**
- SHA-1 hashing (moving to SHA-256)
- Loose objects + packfiles for compression
- Garbage collection based on reachability
- Fast content lookup via sharding

**Limitations for builds:**
- Git objects are immutable (good!)
- No built-in remote execution protocol
- Packfiles complicate random access
- Not optimized for large binary artifacts

---

### Nix Store

**Traditional (input-addressed):**
```
/nix/store/abc123-package-1.2.3/
  ↑ hash(derivation + inputs + build script)
```

**Content-addressed (RFC 0062, experimental):**
```
/nix/store/xyz789-package-1.2.3/
  ↑ hash(output contents)
```

**Content-addressing methods:**
1. **`flat`**: Direct hash of file contents
2. **`nar`** (Nix Archive): Hash of serialized file system object
3. **`git`** (experimental): Git blob/tree hashing for IPFS interop

**Key innovations:**
- **Self-references**: Content-addressed paths can reference themselves
- **Fixed-output derivations**: Legacy content-addressing for fetchurl
- **CA derivations**: Full content-addressing (still experimental)
- **Binary substitution**: Download by hash from any mirror

**Trade-offs:**
- **Pro**: Hermetic, reproducible, deduplicates across users
- **Con**: Can't know output path before building (breaks some workflows)
- **Con**: Input changes force rebuilds even if output identical (without CA)

---

### Bazel/Buck2 Remote Execution API v2

**Architecture:**
```
Client (Bazel/Buck2)
  ↓ Action (hash: abc123)
  ↓ upload inputs via CAS
Remote Execution Service
  ↓ execute action
  ↓ upload outputs to CAS
Client downloads outputs
  ↓ stores in local cache
```

**Content-Addressable Storage (CAS) API:**
- `FindMissingBlobs`: Check which blobs server already has
- `BatchUpdateBlobs`: Upload blobs not in CAS
- `BatchReadBlobs`: Download blobs by hash
- `GetTree`: Fetch entire directory tree

**Action Cache (AC):**
- Maps `Action hash → ActionResult`
- Action hash includes: command, inputs, environment, platform
- ActionResult includes: exit code, stdout/stderr, output hashes

**Key design decisions:**
- **SHA-256** for hashing (collision-resistant, widely supported)
- **Separation**: AC (metadata) vs CAS (blobs) for efficiency
- **Batch operations**: Reduce round-trips for small files
- **Streaming**: ByteStream API for large files (>1MB)
- **Compression**: zstandard compression in transit and at rest (optional)

**Implementation**: BuildBuddy, Buildbarn, EngFlow, Google RBE

---

### IPFS (Inter-Planetary File System)

**Content identifiers (CIDs):**
```
CIDv1: base32(multicodec + multihash(content))
Example: bafybeigdyrzt5sfp7udm7hu76uh7y26nf3efuylqabf3oclgtqy55fbzdi
```

**Components:**
- **Multicodec**: Identifies format (dag-pb, dag-cbor, raw, etc.)
- **Multihash**: Hash algorithm + digest (sha256, blake3, etc.)
- **Chunking**: Large files split using Rabin fingerprinting or fixed-size

**Merkle DAG example:**
```
File (10MB) → CID: Qmabc123
├── Chunk 0 (256KB) → CID: Qmdef456
├── Chunk 1 (256KB) → CID: Qmghi789
└── Chunk 2 (256KB) → CID: Qmjkl012
```

**Key features:**
- **Content-defined chunking**: Rabin/Buzhash for better deduplication
- **Bitswap protocol**: P2P block exchange
- **DHT**: Distributed hash table for content discovery
- **IPLD**: Interplanetary Linked Data (generic Merkle DAG)

**Build system implications:**
- Nix exploring IPFS for binary substitution (via git-hashing)
- Software Heritage Archive uses git-hashing
- Good for distributing artifacts without central server
- **Con**: Discovery overhead, DHT lookups slow vs direct HTTP

---

## 3. Hash Functions for CAS

### Requirements

1. **Cryptographic security**: Collision resistance, pre-image resistance
2. **Performance**: Fast hashing for large files (GB+ artifacts)
3. **Incremental**: Support streaming/chunked hashing
4. **Portability**: Widely supported, stable spec

### Comparison

| Hash Function | Digest Size | Speed (GB/s) | Security | Adoption |
|---------------|-------------|--------------|----------|----------|
| **MD5** | 128-bit | ~3 GB/s | ❌ Broken | Legacy only |
| **SHA-1** | 160-bit | ~2 GB/s | ⚠️ Deprecated | Git (migrating) |
| **SHA-256** | 256-bit | ~1.5 GB/s | ✅ Strong | Bazel, Nix, most |
| **BLAKE2b** | 256-bit | ~3 GB/s | ✅ Strong | Some tools |
| **BLAKE3** | 256-bit | ~10 GB/s | ✅ Strong | Emerging |

### BLAKE3: The Future

**Why BLAKE3 is ideal for build systems:**

1. **Performance**: 10+ GB/s on modern CPUs (SIMD optimized)
   - SSE2, SSE4.1, AVX2, AVX-512, NEON support
   - Automatic CPU feature detection
   - 3-10x faster than SHA-256

2. **Parallelism**: Designed for multi-core and multithreading
   - Can hash across multiple CPU cores
   - Merkle tree structure enables parallel hashing

3. **Incremental**: Efficiently hash streaming data
   - `Hasher::update()` API for chunks
   - Low memory overhead (1912 bytes state)

4. **Verifiable**: Same security level as BLAKE2 and SHA-256
   - 256-bit output (extendable to arbitrary length)
   - No known attacks

5. **Standardization**: Rust `blake3` crate + C reference implementation
   - Used in production: Dropbox, 1Password, others

**Example usage (Rust):**
```rust
use blake3::Hasher;

let mut hasher = Hasher::new();
hasher.update(b"chunk 1");
hasher.update(b"chunk 2");
let hash = hasher.finalize();  // 32-byte output

// For large files
let mut file = File::open("artifact.tar.gz")?;
let mut hasher = Hasher::new();
io::copy(&mut file, &mut hasher)?;
let hash = hasher.finalize();
```

**Adoption trajectory:**
- 2020: BLAKE3 released
- 2021-2024: Gradual adoption in new tools
- 2025+: Likely default for new build systems

**Recommendation for HWML:**
- Use **BLAKE3** for `.hwmli` artifacts and CAS
- SHA-256 for compatibility with existing tools (Bazel REapi)
- Support both via abstraction layer

---

## 4. Storage Tiers and Garbage Collection

### Multi-Tier Storage Strategy

Most build systems use 3 tiers:

**Tier 1: Local build directory** (`.hwml-build/`, `bazel-out/`)
- **Purpose**: Fast access during active build
- **Lifetime**: Disposable, cleaned on `clean`
- **Structure**: Flat or by target/library name

**Tier 2: User-global cache** (`~/.cache/hwml/cas/`)
- **Purpose**: Share artifacts across projects on one machine
- **Lifetime**: Persistent, garbage collected
- **Structure**: Content-addressed, sharded by hash prefix
  ```
  ~/.cache/hwml/cas/ab/cdef123456...
                   ↑↑ first 2 hex chars
  ```
- **Optimization**: Hardlink into Tier 1 (zero-copy on same filesystem)

**Tier 3: Remote shared cache** (BuildBuddy, Buildbarn, S3)
- **Purpose**: Share across team, CI, and time
- **Lifetime**: Long-lived, managed by ops team
- **Protocol**: REapi v2, HTTP, S3
- **Access control**: Read-open, write-restricted to CI

### Garbage Collection Strategies

**Reachability-based (Git, Nix):**
- Mark roots (active refs, recent builds)
- Trace reachable objects
- Delete unreachable objects
- **Pro**: Preserves everything in use
- **Con**: Requires full graph traversal

**LRU with size limit (Bazel, Buck2):**
- Track last access time per artifact
- When cache exceeds size limit, evict oldest
- **Pro**: Predictable space usage
- **Con**: May evict frequently-used-but-old artifacts

**Hybrid (recommended for HWML):**
- Size limit for Tier 2 (e.g., 10 GB)
- LRU eviction when limit exceeded
- Protect recently-accessed artifacts (e.g., last 7 days)
- Command to manually prune: `hwml gc --aggressive`

**Reference counting (complex, avoid):**
- Track which projects reference which artifacts
- Delete when refcount → 0
- **Con**: Hard to maintain correctness across crashes

---

## 5. Case Study: Buck2's DICE + CAS

Buck2 combines two complementary systems:

### DICE: Deterministic Incremental Computation Engine

**Purpose:** In-process incremental computation (like Salsa for Rust Analyzer)

**Architecture:**
```
Client requests compute(key)
  ↓
Shared cache (tasks for in-flight computations)
  ↓
Core state thread (main cache + dependency tracking)
  ↓
Spawn computation if needed
  ↓
Store result with dependencies
```

**Key features:**
1. **Dynamic dependencies**: Computed values can depend on other computed values
2. **Parallel evaluation**: Multiple computations run concurrently (tokio async)
3. **Deduplication**: Multiple requests for same key share computation
4. **Early cutoff**: If value didn't change, downstream skipped

**Early cutoff in DICE:**
- User implements `Key::Value` equality
- If new result `==` cached result, mark as "unchanged"
- Downstream computations reuse cached results
- **Example**: Analysis produces same actions → skip action execution

**Limitations:**
- No equality for analysis results in Buck2 (by design)
- Falls back to other mechanisms (depfile-based matching)

### CAS: Content-Addressable Storage

**Purpose:** Persistent storage for build artifacts

**Flow:**
```
DICE computes action needs to run
  ↓
Check CAS for action cache hit
  ↓ (miss)
Execute action (locally or remotely)
  ↓
Upload outputs to CAS
  ↓
Store action result in action cache
```

**Integration:**
- DICE manages dependency graph + incremental computation
- CAS provides persistent caching across builds + machines
- **Synergy**: DICE (hot cache) + CAS (cold cache) = fast builds

**Why both?**
- DICE: Fast in-process, but lost on restart
- CAS: Slow (network/disk), but persists forever
- Together: Best of both worlds

---

## 6. Salsa's Approach (Rust Analyzer)

Salsa is an incremental computation framework (similar to DICE).

### Core Concepts

**Tracked structs:**
```rust
#[salsa::tracked]
struct Program {
    #[id] source: SourceFile,
    statements: Vec<Statement>,
}
```

- Each field has a **revision** when it last changed
- When recreating in new revision: compare old vs new values
- If unchanged: don't propagate revision change downstream

**Tracked functions:**
```rust
#[salsa::tracked]
fn parse(db: &dyn Db, source: SourceFile) -> Program {
    // ...
}
```

- Memoized: cache result keyed by inputs
- Track dependencies: which other tracked functions were called
- Incremental re-execution: rerun only if dependencies changed

### Durability System (optimization)

**Problem:** Not all inputs change at the same rate

**Solution:** Assign durability levels
- **Volatile**: Source files of current project
- **Durable**: Source files of standard library

**Version vector:**
```
[volatile_version, durable_version]
```

- Changing volatile input increments `volatile_version`
- Changing durable input increments `durable_version`
- Derived queries track their minimum durability
- Check: compare query's version against corresponding level

**Benefit:** Editing project file doesn't invalidate std lib queries

### Comparison with CAS

| Aspect | Salsa | CAS |
|--------|-------|-----|
| **Scope** | In-process, single invocation | Persistent, cross-invocation |
| **Granularity** | Function calls | File artifacts |
| **Storage** | Memory (hashtables) | Disk / remote server |
| **Verification** | Rust types | Cryptographic hashes |
| **Use case** | IDE responsiveness | Build caching |

**For HWML:**
- Use **Salsa** for in-process elaboration caching
- Use **CAS** for `.hwmli` artifact caching
- Similar to Buck2's DICE + CAS model

---

## 7. Build System Databases

### Ninja: `.ninja_deps` and `.ninja_log`

**`.ninja_log`** (build log):
- Records completed builds: `<start> <end> <restat_mtime> <target> <command_hash>`
- Enables command-line change detection
- Used for ETA prediction (previous execution times)

**`.ninja_deps`** (dependency log):
- Stores implicit dependencies discovered via depfiles
- Binary format for fast loading
- Structure:
  ```
  path_id → path_string  (path interning)
  output_id → [input_id, input_id, ...]  (dependency edges)
  ```
- Loaded at startup, augments dependency graph

**Key insight:**
- **Static deps**: Declared in `build.ninja`
- **Implicit deps**: Discovered during build (e.g., `#include` headers)
- **Dynamic deps** (dyndep): Loaded before build from generated files

**Limitations:**
- Mtime-based (not content-addressed)
- No remote caching
- Requires higher-level build system (CMake, Meson) to generate `build.ninja`

### Shake: Persistent cache

**Data model:**
```haskell
database :: File -> (ModTime, [(File, ModTime)])
```

- For each `File`, store: last `ModTime`, list of dependencies + their `ModTimes`
- On rebuild: check if dependency `ModTime`s changed
- **Optimization**: Store `Step` (build number) instead of `ModTime` for faster checks

**Persistent storage:**
- `.shake.database` file (binary serialization)
- Loaded at startup, saved at shutdown
- Contains full build history + profiling data

**Cloud Shake (experimental):**
- Share cache via `--share=LOCATION`
- Upload/download cached results
- Requires build to be reproducible (hermetic)

**Key insight:**
- Shake is more like a library than a tool
- Flexible enough to embed custom logic
- Database format is implementation detail (opaque)

---

## 8. Academic Foundations

### "Build Systems à la Carte" (Mokhov et al., ICFP 2018)

**Key insight:** Build systems vary along 2 axes:

1. **Scheduling** (how to execute tasks):
   - **Topological**: Sort dependencies, execute in order (Make)
   - **Restarting**: Execute, restart if new dependencies discovered (Excel)
   - **Suspending**: Pause execution until dependencies available (Shake, Bazel)

2. **Rebuilding** (when to re-execute tasks):
   - **Dirty bit**: Mark changed inputs (Make)
   - **Verifying traces**: Compare current inputs to cached inputs (Shake)
   - **Constructive traces** (CT): Rebuild if any dependency's trace changed (Bazel)
   - **Deep constructive traces** (DCT): Also check transitive dependencies (Buck2)

**Persistent build information:**
- **Make**: Modification times (mtimes)
- **Shake**: `(value, dependencies, dependency_traces)` per key
- **Bazel**: Hashes of inputs, outputs, command
- **Buck2**: Full Merkle tree of inputs + action graph

**Early cutoff:**
- If task re-executes but produces same output → downstream skipped
- Requires output comparison (equality or hash)
- **Make**: No early cutoff (always propagates rebuilds)
- **Shake, Bazel, Buck2**: Support early cutoff

### "A Sound and Optimal Incremental Build System" (Erdweg et al., OOPSLA 2015)

**Pluto build system:**
- Tracks dynamic dependencies at runtime
- Proves soundness (always produces correct output)
- Proves optimality (never does unnecessary work)

**Key mechanisms:**
1. **Interleave dependency analysis and execution**
   - Discover dependencies as you go (like Excel, Shake)
2. **Fine-grained triggers**
   - Builder can specify subset of inputs that trigger rebuild
3. **Cyclic dependencies**
   - Iterate to fixed point
4. **Internal consistency checks**
   - Validate cached results are still valid

**Formalization:**
- Build units, builders, build inputs
- Incrementality properties: minimize executions + checks
- Proof that Pluto satisfies both

**Relevance to HWML:**
- Dependently-typed elaboration has dynamic dependencies
- Importing module A might require elaborating module B on-the-fly
- Pluto's model could formalize HWML's elaboration caching

---

## 9. Recommendations for HWML

### CAS Architecture

**Hash function:** BLAKE3
- 10x faster than SHA-256
- Secure, standardized, well-supported
- Future-proof (new build systems will adopt)

**Storage tiers:**
1. **Project local**: `.hwml-build/<lib>-<hash>.hwmli`
2. **User global**: `~/.cache/hwml/cas/ab/cdef...`
   - Sharded by first 2 hex chars
   - Hardlinked into project local
3. **Remote**: REapi v2-compatible server (BuildBuddy, Buildbarn)
   - Read: open to all developers
   - Write: restricted to CI (ensures hermetic builds)

**Garbage collection:**
- Size limit for Tier 2 (default 10 GB, configurable)
- LRU eviction when limit exceeded
- Protect artifacts accessed in last 7 days
- `hwml gc` command for manual cleanup

### Integration with Salsa

**In-process (Salsa):**
- Track elaboration queries (e.g., `elaborate_library`)
- Memoize results in memory
- Incremental re-elaboration within single `hwml build` session

**Persistent (CAS):**
- Serialize elaborated libraries to `.hwmli`
- Store in CAS keyed by BLAKE3 hash
- Load from cache on next invocation

**Hybrid workflow:**
```
hwml build
 ↓
 Load workspace (Salsa input)
 ↓
 For each library in topo order:
   ↓
   Compute .hwmli hash = BLAKE3(sources + dependencies)
   ↓
   Check Tier 1 cache → Tier 2 cache → Tier 3 cache
   ↓ (cache miss)
   Elaborate library (Salsa memoization within this step)
   ↓
   Serialize .hwmli
   ↓
   Store in all cache tiers
```

**Early cutoff:**
- Per-declaration fingerprints (like GHC)
- Usage tracking: record which declarations were actually used
- On rebuild: if used declarations unchanged → skip re-elaboration
- Stored in `.hwmli` metadata

### Remote Execution Integration

**Option 1: REapi v2 native**
- Implement REapi client in `hwml`
- `hwml build --remote_executor=grpc://buildbuddy.example.com`
- Actions: `elaborate library X`
- Inputs: source files, dependency `.hwmli` files
- Outputs: library `.hwmli` file

**Option 2: Buck2/Nix orchestration**
- Generate `BUCK` or Nix derivation from `hwml.toml`
- Buck2/Nix handle remote execution
- `hwml` compiler is just an action
- Leverage their caching infrastructure

**Recommendation:** Support both
- Option 1 for standalone users
- Option 2 for large orgs with existing Buck2/Nix

---

## 10. Open Questions and Future Work

### 1. Content-Addressing vs Input-Addressing

**Trade-off:**
- **Input-addressing**: Know output path before building (easier for build systems)
- **Content-addressing**: Deduplication, early cutoff, unprivileged copying

**Nix's experience:**
- RFC 0062 (CA derivations) still experimental after 4+ years
- Challenges: self-references, rewriting paths, tooling complexity

**For HWML:**
- Start with input-addressing (hash of dependencies + sources)
- Explore content-addressing later (once basic system works)
- Use content-addressing for CAS lookup (but input-addressing for paths)

### 2. Hashing Entire `.hwmli` vs Per-Declaration

**Whole-file hash:**
- **Pro**: Simple, easy to implement
- **Con**: Any change invalidates entire file

**Per-declaration hash:**
- **Pro**: Fine-grained invalidation (GHC-style early cutoff)
- **Con**: Complex bookkeeping, larger `.hwmli` metadata

**Recommendation:**
- Phase 1: Whole-file hash
- Phase 4: Per-declaration hash (with usage tracking)

### 3. Compression in CAS

**Options:**
- **Uncompressed**: Fast, large disk usage
- **zstd**: Good ratio, fast decompression (~500 MB/s)
- **zstd with custom dictionary**: Better ratio for similar files

**Bazel/Buck2 approach:**
- Store compressed in CAS
- Decompress on download
- Optional: download compressed via `compressed-blobs` extension

**Recommendation:**
- Store `.hwmli` files compressed (zstd level 3) in Tier 2 and Tier 3
- Uncompressed in Tier 1 for fast access
- ~60-80% size reduction expected for elaborated ASTs

### 4. Deduplication Granularity

**File-level (current plan):**
- Each `.hwmli` is one CAS object
- Duplication if two libraries differ by one declaration

**Declaration-level (future):**
- Store each declaration as separate CAS object
- `.hwmli` is manifest of declaration hashes
- Perfect deduplication

**Trade-off:**
- Declaration-level: More complex, more CAS operations
- File-level: Simpler, fewer round-trips

**Recommendation:** File-level for MVP, explore declaration-level later

---

## 11. Summary: CAS Design for HWML

### Chosen Approach

**Hash function:** BLAKE3 (256-bit)
**Storage tiers:**
1. Local build dir (disposable)
2. User-global CAS (`~/.cache/hwml/cas/`, sharded, hardlinked)
3. Remote REapi v2 server (BuildBuddy/Buildbarn)

**Addressing:** Input-addressed paths + content-addressed CAS
**Early cutoff:** Per-declaration fingerprints + usage tracking (Phase 4)
**Compression:** zstd for Tier 2/3 storage
**GC:** LRU with size limit + recency protection

### Implementation Phases

**Phase 1: Local CAS (Tier 1 + Tier 2)**
- BLAKE3 hashing of `.hwmli` files
- Tier 1: `.hwml-build/<lib>-<hash>.hwmli`
- Tier 2: `~/.cache/hwml/cas/ab/cdef...`
- Hardlink from Tier 2 to Tier 1

**Phase 2: Basic GC**
- Size limit configuration
- LRU eviction
- `hwml gc` command

**Phase 3: Remote CAS (Tier 3)**
- REapi v2 client
- Upload on build (if remote_cache configured)
- Download on cache miss

**Phase 4: Early Cutoff**
- Per-declaration fingerprints
- Usage tracking in `.hwmli`
- GHC-style recompilation avoidance

**Phase 5: Buck2/Nix Integration**
- Generate `BUCK`/Nix from `hwml.toml`
- Integrate with their CAS
- Hermetic remote execution

### Success Metrics

- [ ] Cache hit rate >80% on incremental builds
- [ ] Cross-user deduplication (multiple checkouts share cache)
- [ ] Remote cache reduces CI time by >50%
- [ ] Early cutoff skips >90% of unchanged downstream rebuilds
- [ ] BLAKE3 hashing completes in <10% of elaboration time
- [ ] GC maintains cache under size limit without manual intervention

---

## References

### Papers
- Mokhov et al., "Build Systems à la Carte", ICFP 2018
- Erdweg et al., "A Sound and Optimal Incremental Build System with Dynamic Dependencies", OOPSLA 2015
- Mitchell, "Shake Before Building", ICFP 2012

### Systems
- Buck2: https://buck2.build/
- Bazel Remote APIs: https://github.com/bazelbuild/remote-apis
- Nix RFC 0062: https://github.com/NixOS/rfcs/blob/master/rfcs/0062-content-addressed-paths.md
- Salsa: https://github.com/salsa-rs/salsa
- BLAKE3: https://github.com/BLAKE3-team/BLAKE3

### Tools
- BuildBuddy: https://www.buildbuddy.io/
- Buildbarn: https://github.com/buildbarn/bb-storage
- IPFS: https://ipfs.tech/

---

**Related ADRs:**
- [[decisions/ADR-004-mvs-package-manager]] - Package management
- [[decisions/ADR-006-multi-layer-build-configuration]] - Build configuration
- [[research/incremental-compilation-synthesis]] - Overall incremental strategy
- [[research/modern-build-systems]] - Build system comparison

**Next Steps:**
1. Prototype BLAKE3 hashing for `.hwmli` serialization
2. Implement Tier 1 + Tier 2 CAS (local caching)
3. Design `.hwmli` format with per-declaration metadata
4. Measure cache hit rates on real-world hardware projects
