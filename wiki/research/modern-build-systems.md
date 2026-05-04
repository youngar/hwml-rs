# Modern Build Systems: CAS, Remote Execution, and Hermeticity

**Created:** 2026-05-03  
**Type:** Research Synthesis  
**Status:** Industry systems analysis (2020-2026)  
**Confidence:** 0.95 (based on production system documentation)

---

## Summary

Modern build systems achieve fast, correct, reproducible builds through **content-addressable storage (CAS)**, **remote execution APIs**, and **hermetic build environments**. The ecosystem has standardized around Bazel's Remote Execution API v2, with multiple compatible implementations.

---

## Content-Addressable Storage (CAS)

### Core Principle

**Every artifact is addressed by its content hash** (usually SHA-256).
- Identical content → same hash → stored once
- Changes → different hash → new storage
- Enables perfect deduplication across users, machines, and time

### Key Benefits

1. **Deduplication**: Common dependencies (base images, stdlib) stored once per organization/instance
2. **Cache sharing**: Different users building same code reuse artifacts
3. **Verification**: Hash mismatch detects corruption or tampering
4. **Reproducibility**: Content-addressed artifacts are immutable

### Implementation Patterns

**Bazel/Buck2/BuildStream:**
```
Action Cache (AC):  action_hash → (result metadata, output digests)
Content-Addressable Store (CAS): digest → blob data
```

**Workflow:**
1. Compute action hash (input files + command + env)
2. Query AC: cache hit? → download outputs from CAS
3. Cache miss? → execute → upload outputs to CAS → store result in AC

**Compression:** Most systems support zstandard compression for blobs to reduce storage and network costs.

### Deduplication Scope

**Instance-wide** (Bazel default):
- All users share one CAS
- Maximum deduplication
- Requires trust/permissions model

**Organization-scoped** (GitLab Artifact Registry ADR-002):
- CAS shared within organization, isolated between organizations
- Balance between deduplication and isolation
- Prevents cross-org cache poisoning

**Project-scoped** (GitHub Actions cache):
- Repository-scoped, 10GB default limit
- Less deduplication, but simpler permissions

**References:**
- [Bazel Remote Caching](https://docs.bazel.build/versions/3.2.0/remote-caching.html)
- [GitLab ADR-002: Storage Deduplication Scope](https://handbook.gitlab.com/handbook/engineering/architecture/design-documents/artifact_registry/decisions/002_storage_deduplication_scope/)

---

## Remote Execution API

### Bazel Remote Execution API v2

The de facto standard for distributed builds.

**Supported by:**
- Bazel, Buck2, BuildStream, Pants, Recc, Reclient
- Servers: Buildbarn, BuildBuddy, NativeLink, bazel-remote

**Core Services:**
1. **Execution**: Execute action on remote worker
2. **ActionCache**: Map action hash → result metadata
3. **ContentAddressableStorage**: Store/retrieve blobs by digest
4. **ByteStream**: Stream large files

**Protocol:**
- gRPC-based (high performance, bi-directional streaming)
- Also HTTP/1.1 for simple caching (PUT/GET at `/ac/` and `/cas/` paths)

**Key Features:**
- **Action deduplication**: Multiple clients requesting same action → single execution
- **Platform properties**: Request specific execution environment (OS, arch, CPU, memory)
- **Timeouts**: Client specifies max execution time, server can extend/reduce
- **Streaming**: Results streamed as available (stdout, stderr, output files)

**Example Flow:**
1. Client uploads inputs to CAS
2. Client creates Action (input digest, command, platform properties)
3. Client calls Execute(action_digest)
4. Server checks ActionCache for previous result
5. Cache miss → schedule on worker with matching platform
6. Worker downloads inputs from CAS
7. Worker executes in container/sandbox
8. Worker uploads outputs to CAS
9. Server stores ActionCache entry (action → output digests)
10. Server streams results to client

**References:**
- [Bazel Remote Execution API spec](https://github.com/bazelbuild/remote-apis/)
- [Remote Execution Overview](https://preview.bazel.build/remote/rbe)

---

## Hermetic Builds

### Definition

**Hermetic build**: Given identical inputs, always produces bit-for-bit identical outputs, regardless of:
- When the build runs (today vs next year)
- Where it runs (developer machine vs CI vs remote executor)
- What's installed on the host system

### Key Principles

1. **Explicit dependencies**: All inputs declared (source files, tools, libraries)
2. **Isolated execution**: Sandboxed from host filesystem, network, devices
3. **Deterministic outputs**: No timestamps, random numbers, or machine-specific paths
4. **Pinned toolchains**: Specific versions of compilers, not "whatever is installed"

### Common Sources of Non-Determinism

- **Timestamps**: `__DATE__`, `__TIME__` macros, file modification times in archives
- **Random**: Random number generators, hash iteration order (dictionaries)
- **Filesystem**: Absolute paths, directory traversal order, `/tmp` contents
- **Environment**: `$HOME`, `$USER`, `$RANDOM`, timezone
- **Parallelism**: Race conditions, thread scheduling, memory layout

### Mitigation Strategies

**Bazel/Buck2:**
- Run all actions in sandbox (separate mount namespace on Linux)
- Clear/controlled environment variables
- Deterministic `SOURCE_DATE_EPOCH` for timestamps
- Hermetic toolchains (downloaded, not system-installed)

**Nix:**
- Builds in isolated `/tmp` directory with no network access
- All dependencies via store paths (content-addressed)
- Builds as special user with no home directory
- Fixed timestamps in output archives (epoch 0 or last Git commit)

**Buck2 vs Bazel:**
- Bazel: Sandboxes even local builds (slight overhead, strong hermeticity)
- Buck2 (OSS): No local sandbox, relies on discipline ("remote first")
- Buck2 (Meta internal): Always uses remote execution, hermeticity enforced server-side

**Floating Content-Addressed Derivations (Nix CA):**
- Experimental feature: Output paths based on content hash, not input hash
- Enables better caching even when build method changes
- Requires deterministic builds (otherwise hash differs, cache miss)

**References:**
- [Hermeticity - Bazel](https://docs.bazel.build/versions/master/hermeticity.html)
- [Nix Content-Addressed Derivations](https://wiki.nixos.org/wiki/Ca-derivations)
- [Buck2: Why Buck2?](https://buck2.build/docs/why/)

---

## Production Systems

### Buck2 (Meta)

**Architecture:**
- Core: Rust (performance, correctness)
- Rules: Starlark (extensibility)
- **Single incremental dependency graph** (no phases like Bazel/Buck1)
- **Dynamic dependencies**: Monadic graph, actions can discover dependencies

**Key Innovation:**
- 2x faster than Buck1
- Totally language-agnostic core
- BXL (Buck Extension Language) for build introspection

### BuildBuddy / Buildbarn

**BuildBuddy:** Commercial RBE service
- Auto-scaling executors
- Three-tier caching (memory, disk, cloud)
- Live action view (watch remote builds in real-time)
- Remote Bazel (run bazel itself remotely, not just actions)

**Buildbarn:** OSS RBE implementation
- `bb-storage`: CAS + AC
- `bb-scheduler`: Dispatch actions to workers
- `bb-worker` + `bb-runner`: Execute actions

### NativeLink

**Nix-powered RBE:**
- Rust implementation of RE API v2
- Compatible with Bazel, Buck2, Soong, Pants
- High performance (async tokio)

**References:**
- [Buck2 Architecture](https://github.com/facebook/buck2/blob/main/docs/developers/architecture/buck2.md)
- [BuildBuddy RBE](https://buildbuddy.io/docs/remote-build-execution)
- [NativeLink](https://github.com/TraceMachina/nativelink)

---

## Continued in Part 3...

**See:** [[research/lsp-and-remote-compilation]] for LSP integration with remote builds.
