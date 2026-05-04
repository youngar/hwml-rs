# ADR-006: Multi-Layer Build Configuration System

**Status:** Proposed
**Date:** 2026-05-03
**Deciders:** Core team
**Related:** [[ADR-004-mvs-package-manager]], [[research/modern-build-systems]], [[research/buck2-integration-patterns]], [[research/build-system-caching-synthesis]]

---

## Context

HWML needs a build configuration system that supports:
- Library-level dependency management (like Cargo, npm)
- Workspace/monorepo builds (like Cargo workspaces, Nx)
- Multiple build configurations (FPGA, ASIC, simulation)
- Remote execution and artifact caching
- Fast LSP with clear build context
- Integration with external build systems (Buck2, Nix)
- Local development across multiple workspaces

Current approach is unclear: how do we specify dependencies, build settings, toolchain versions, and cache configuration?

**Key Requirements:**
1. Library authors declare dependencies without build details
2. Build engineers configure targets, optimization, caching
3. End users have simple workflow (`hwml build`)
4. LSP knows which build context to use
5. Support local development with quick turnaround
6. Integrate with Buck2/Nix for large organizations
7. Enable remote execution and cross-user caching

---

## Decision

We adopt a **three-layer build configuration system**:

### Layer 1: Library Manifest (`hwml.toml`)
Per-library file declaring dependencies and metadata.

**Purpose:** What this library is and what it needs  
**Location:** `lib/uart/hwml.toml` (checked into version control)  
**Maintained by:** Library authors

```toml
[package]
name = "uart-controller"
version = "0.2.1"
authors = ["Your Name <you@example.com>"]
license = "MIT OR Apache-2.0"
description = "Configurable UART controller with FIFO buffering"
edition = "2026"

# Source file elaboration order (optional)
# If omitted: alphabetical glob of *.hwml files in library root
[sources]
files = ["types.hwml", "impl.hwml", "testbench.hwml"]

# Entry points
[lib]
path = "src/lib.hwml"

[[bin]]
name = "uart-testbench"
path = "tests/tb_uart.hwml"

[dependencies]
# Local path references (development)
fifo = { path = "../fifo" }

# External versioned dependencies (MVS resolution)
std = "1.4.2"
axi4 = "^2.1"

[dev-dependencies]
simulation-utils = "0.1"

[features]
default = ["fifo-overflow-protection"]
debug-ports = []
fifo-overflow-protection = ["fifo/overflow-checks"]
```

**Key properties:**
- Immutable per library (part of source tree)
- No build settings (target, optimization, caching)
- Only declares dependencies and features
- Similar to Cargo's `Cargo.toml`, npm's `package.json`

**Important sections:**

- **`[package]`**: Library metadata (name, version, authors, license, description, edition)
  - Edition controls language features (like Rust editions: 2015, 2018, 2021)
  - Version uses SemVer; breaking changes → new import path (`my-lib/v2`)

- **`[sources]`** (optional): Controls elaboration order within library
  - Default: alphabetical glob of `*.hwml` files
  - Explicit ordering needed for forward references between files
  - Future: two-pass elaboration will remove this constraint

- **`[lib]` and `[[bin]]`**: Entry points
  - `[lib]`: Main library code (one per package)
  - `[[bin]]`: Testbenches, utilities (multiple allowed)
  - Distinguishes library interface from test/utility code

- **`[dependencies]`**: Required dependencies
  - Path deps: `{ path = "../fifo" }` for local development
  - Registry deps: `"1.4.2"` or `"^2.1"` for MVS resolution

- **`[dev-dependencies]`**: Only for tests/benchmarks, not included in library interface

- **`[features]`**: Conditional compilation flags
  - `default = [...]`: Features enabled by default
  - Features can enable other features transitively
  - Can make dependencies optional: `dep = { version = "1.0", optional = true }`

---

### Layer 2: Workspace/Build Configuration (`hwml-workspace.toml`, `builds/*.toml`)

**Purpose:** What to build and how to build it  
**Location:** Repository root or per-build-config  
**Maintained by:** Build engineers, infrastructure team

**Workspace file (`hwml-workspace.toml`):**
```toml
[workspace]
members = ["lib/uart", "lib/fifo", "top/soc"]
exclude = ["external/*"]

# Shared dependencies across workspace
[workspace.dependencies]
std = "1.4.2"

[workspace.lsp]
cache-priming = "parallel"
max-cache-size-mb = 2048
watch-mode = "server"
fetch-remote-hwmli = true
```

**Build configuration file (`builds/fpga.toml` or `hwml-build.toml`):**
```toml
[build]
target = "fpga-xilinx-ultrascale"
optimization = "size"
profile = "release"

[features]
uart-controller = ["debug-ports"]
std = ["verbose-assertions"]

[output]
top-module = "soc"
format = "verilog"

[cache]
local = "~/.cache/hwml"
remote = "https://cache.company.com"
use-remote-execution = true

[toolchain]
hwml-version = "0.3.0"
circt-version = "1.44.0"

[targets.fpga-xilinx-ultrascale]
backend = "circt"
constraints = { clock-period = "10ns" }

# Development overrides (not committed)
[dependencies.overrides]
# library-a = { path = "../../other-workspace/lib/library-a" }
```

**Key properties:**
- **Not** typically in library repos (build-specific)
- Specifies build targets, optimization, features
- Configures caching and remote execution
- May be committed to top-level project repos
- Can have multiple build configs (FPGA, ASIC, sim)

---

### Layer 3: Lock File (`hwml.lock`)

**Purpose:** Resolved dependency graph with exact versions  
**Location:** Repository root (alongside workspace file)  
**Maintained by:** Tool (auto-generated)

```toml
# Auto-generated by hwml. DO NOT EDIT.
version = 1

[[package]]
name = "uart-controller"
version = "0.2.1"
source = "path+../lib/uart"

[[package]]
name = "std"
version = "1.4.2"
source = "registry+https://hwml.org/registry"
checksum = "sha256:abc123..."

[[package]]
name = "fifo"
version = "0.1.3"
source = "path+../lib/fifo"

[[package]]
name = "axi4"
version = "2.1.0"
source = "registry+https://hwml.org/registry"
checksum = "sha256:def456..."

[metadata]
solver-version = "0.3.0"
solved-by-build = "builds/fpga.toml"
resolved-at = "2026-05-03T10:00:00Z"
```

**Key properties:**
- Generated by MVS solver
- Locks exact versions for reproducibility
- Committed to version control
- Updated by `hwml update` or when dependencies change

---

## Consequences

### Positive

1. **Clear separation of concerns:**
   - Library authors: dependencies only
   - Build engineers: targets, caching, toolchain
   - End users: simple workflow

2. **Multiple build configurations:**
   - Same codebase builds for FPGA, ASIC, simulation
   - Different optimization levels (debug, release, CI)
   - Switch builds easily: `hwml use-build builds/asic.toml`

3. **LSP clarity:**
   - Reads workspace root (`hwml-workspace.toml`)
   - Uses active build (`.hwml/active-build.toml`)
   - Clear context for dependency resolution

4. **Local development support:**
   - Path overrides for cross-workspace dev
   - Temporary workspace combining multiple repos
   - Local registry for quick iteration

5. **Buck2/Nix integration:**
   - `hwml.toml` is source of truth
   - External build systems read it
   - Generate Buck2 `BUCK` files or Nix derivations
   - Leverage their caching/remote execution

6. **Incremental adoption:**
   - Simple projects: just `hwml.toml` + defaults
   - Complex projects: workspace + multiple build configs
   - Enterprise: Buck2/Nix orchestration

7. **Reproducibility:**
   - Lock file ensures exact versions
   - Build file pins toolchain versions
   - Hermetic builds by default

### Negative

1. **Complexity:**
   - Three layers to understand (vs single file)
   - Mitigation: Good defaults, simple projects need only `hwml.toml`

2. **Build file discovery:**
   - Which build config to use?
   - Mitigation: Sensible defaults, explicit `hwml use-build`

3. **Path override confusion:**
   - When to use path vs version?
   - Mitigation: Clear documentation, linting

4. **Lock file conflicts:**
   - Merge conflicts on `hwml.lock`
   - Mitigation: Like Cargo, conflicts resolved by re-running solver

5. **Integration complexity:**
   - Buck2/Nix integration requires tooling
   - Mitigation: Provide generators (`hwml generate buck`, `hwml generate nix`)

---

---

## Implementation: `hwml-workspace` Crate

A new crate `hwml-workspace` will handle manifest parsing, dependency resolution, and workspace management. It does **not** depend on `hwml-core` or `hwml-elab`.

**Core types:**

```rust
pub struct LibraryManifest {
    pub name: String,
    pub version: semver::Version,
    pub edition: u32,
    pub root: PathBuf,               // canonical absolute path
    pub source_files: Vec<PathBuf>,  // relative to root, elaboration order
    pub dependencies: Vec<LibraryDep>,
    pub features: HashMap<String, Vec<String>>,
}

pub struct LibraryDep {
    pub name: String,
    pub version_req: semver::VersionReq,   // for human display
    pub source: LibraryDepSource,
}

pub enum LibraryDepSource {
    Path(PathBuf),
    Registry { url: String, version: String, source_hash: [u8; 32] },
}

pub struct Workspace {
    pub libraries: IndexMap<String, LibraryManifest>,  // name → manifest
    pub topo_order: Vec<String>,   // leaves first, root last
}

pub enum WorkspaceError {
    ManifestNotFound(PathBuf),
    CycleDetected(Vec<String>),    // cycle path for error message
    DuplicateLibrary { name: String, first: PathBuf, second: PathBuf },
    Io(PathBuf, io::Error),
    Toml(PathBuf, toml::de::Error),
}

impl Workspace {
    /// Walk manifest, load transitive deps, cycle-detect, topo-sort.
    pub fn load(root: PathBuf) -> Result<Workspace, WorkspaceError>;

    /// Search upward from `start` for hwml.toml (cargo-style discovery).
    pub fn find_manifest(start: &Path) -> Option<PathBuf>;
}
```

**Crate dependency graph:**

```
hwml-workspace (new)
  → toml            (manifest parsing)
  → semver          (version parsing, MVS)
  → petgraph        (topo-sort, cycle detection)
  ← hwml            (CLI uses it)
  ← hwml-lsp-server (workspace open, file watching)

hwml-db
  → hwml-workspace  (LibraryManifest as Salsa input)
  → hwml-surface    (parse_surface_file)
```

**Source file discovery:**
1. If `[sources]` specified: use that order
2. Else: alphabetical glob of `*.hwml` files in library root
3. Validate all files exist before compilation

---

## Implementation Details

### File Discovery and Precedence

**LSP startup:**
1. Find workspace root: Walk up from current file until `hwml-workspace.toml` found
2. Check `.hwml/active-build.toml` for user-selected build
3. If none, use default from workspace or `hwml-build.toml` in root
4. Load dependency resolution from lock file
5. Apply feature flags from build config

**CLI build:**
```bash
# Use default build (hwml-build.toml or workspace default)
hwml build

# Use specific build config
hwml build --config builds/fpga.toml

# Set active build (persisted to .hwml/active-build.toml)
hwml use-build builds/asic.toml
```

---

### Local Development Across Workspaces

**Scenario:** Working on library A (workspace-1) and library B (workspace-2), need quick turnaround.

**Solution 1: Path Override (Recommended)**
```toml
# workspace-2/hwml-build.toml (not committed, personal)
[dependencies.overrides]
library-a = { path = "../../workspace-1/lib/library-a" }
```

**Solution 2: Temporary Combined Workspace**
```toml
# workspace-dev/hwml-workspace.toml
[workspace]
members = [
    "../workspace-1/lib/library-a",
    "../workspace-2/lib/library-b",
]
```

**Solution 3: Local Registry**
```bash
# In workspace-1
hwml publish --local ~/.cache/hwml/local-registry

# In workspace-2/hwml-build.toml
[cache]
local-registry = "~/.cache/hwml/local-registry"
```

---

### Buck2 Integration

**Approach:** `hwml.toml` → Buck2 targets

**Generator tool:**
```bash
# Generate BUCK files from hwml.toml
hwml generate buck --workspace .
```

**Generated BUCK file:**
```python
load("@hwml//rules:hwml.bzl", "hwml_library")

hwml_library(
    name = "uart",
    srcs = glob(["src/**/*.hwml"]),
    deps = [
        "//lib/fifo:fifo",
        "@hwml-registry//std:1.4.2",
    ],
    features = ["debug-ports"],
    edition = "2026",
    visibility = ["//visibility:public"],
)
```

**Key benefits:**
- Buck2 orchestrates builds (parallelism, remote execution, hermetic)
- `hwml` compiler is Buck2 action (cacheable in CAS)
- `.hwmli` artifacts stored in Buck2's content-addressed cache
- Integrates with polyglot monorepo

**Workflow:**
```bash
# Buck2 reads hwml.toml, generates dependency graph
buck2 build //lib/uart:uart

# Buck2 executes hwml compiler with remote execution
# Stores .hwmli in CAS
# Reuses across builds and developers
```

**Persistent Worker Support:**

To achieve both Buck2's hermeticity and fast local builds, the `hwml` compiler will implement the Persistent Worker Protocol:

```bash
# Buck2 starts compiler in worker mode
hwml --persistent_worker

# Compiler enters loop reading WorkRequests from stdin
# Keeps ASTs in memory between compilations
# 10-100x faster than cold-start per module
```

**Why persistent workers:**
- **Problem**: Cold-start CLI per module → slow (boot overhead every time)
- **Solution**: Long-running process that keeps parsed ASTs in memory
- **Buck2 compatibility**: Buck2 sends JSON requests via stdin, gets responses via stdout
- **Hermeticity maintained**: Buck2 controls exact inputs/outputs, no hidden caches
- **Performance**: Java, Scala, Rust achieve fast Buck2 builds this way

See [[research/buck2-integration-patterns]] for detailed architecture.

---

### Nix Integration

**Approach:** `hwml.toml` → Nix derivation

**Generator tool:**
```bash
# Generate default.nix from hwml.toml
hwml generate nix --workspace .
```

**Generated Nix derivation:**
```nix
{ stdenv, hwml, lib, fetchFromGitHub }:

let
  # Dependency on std from registry
  std = stdenv.mkDerivation {
    name = "hwml-std-1.4.2";
    src = fetchFromGitHub {
      owner = "hwml-lang";
      repo = "std";
      rev = "v1.4.2";
      sha256 = "abc123...";
    };
    buildInputs = [ hwml ];
    installPhase = "hwml build --output $out";
  };

  # Local dependency
  fifo = import ../fifo { inherit stdenv hwml lib; };

in stdenv.mkDerivation {
  name = "uart-controller-0.2.1";
  src = ./.;

  buildInputs = [ hwml ];
  propagatedBuildInputs = [ std fifo ];

  buildPhase = ''
    hwml build \
      --features debug-ports \
      --output $out/lib/uart.hwmli
  '';

  # Content-addressed output (Nix CA derivations)
  __contentAddressed = true;
  outputHashMode = "recursive";
  outputHashAlgo = "sha256";
}
```

**Key benefits:**
- Hermetic builds (sandbox, no network)
- Reproducible across time and machines
- Content-addressed derivations for deduplication
- Integrates with NixOS infrastructure

---

### Build Profiles

Similar to Rust's profiles, we support named build configurations:

```toml
[profile.dev]
optimization = "none"
debug-info = "full"
assertions = true
incremental = true

[profile.release]
optimization = "aggressive"
debug-info = "source-maps"
assertions = false
incremental = false

[profile.ci]
optimization = "size"
debug-info = "minimal"
warnings-as-errors = true
```

**Usage:**
```bash
hwml build --profile release
hwml test --profile ci
```

---

### Feature System

**In library (`hwml.toml`):**
```toml
[features]
default = ["std"]

# Additive features
debug-ports = []
fifo-overflow = ["fifo/overflow-checks"]

# Optional dependencies (only included if feature enabled)
verbose-logging = ["log-utils"]

[dependencies]
fifo = "0.1"
log-utils = { version = "1.0", optional = true }
```

**In build config:**
```toml
[features]
uart-controller = ["debug-ports", "verbose-logging"]
```

**CLI override:**
```bash
hwml build --features "uart-controller/debug-ports"
hwml build --no-default-features
```

---

## Alternatives Considered

### Alternative 1: Single File (Rejected)

**What:** Everything in `hwml.toml`

**Why rejected:**
- Mixes library concerns with build concerns
- Can't have multiple build configurations
- Hard to integrate with Buck2/Nix
- No clean separation for workspaces

---

### Alternative 2: Package.json + Makefile Style (Rejected)

**What:** Dependencies in `hwml.toml`, build in `Makefile` or scripts

**Why rejected:**
- Not declarative (scripts are imperative)
- Harder to integrate with remote execution
- No standard format for tooling (LSP, Buck2, Nix)
- Build logic scattered

---

### Alternative 3: Buck2-Only (Rejected)

**What:** Use Buck2 `BUCK` files for everything

**Why rejected:**
- Forces Buck2 adoption (not everyone wants it)
- Not suitable for small projects
- Hard to migrate to/from other ecosystems
- Buck2 syntax less familiar than TOML

---

### Alternative 4: Nix-Only (Rejected)

**What:** Use Nix derivations for everything

**Why rejected:**
- Steeper learning curve than TOML
- Slower iteration (Nix sandbox overhead)
- Not suitable for non-Nix users
- Hard to get started for new users

---

## Migration Path

### Phase 1: Single Library Projects
- Just `hwml.toml` required
- Defaults for build settings
- Lock file generated automatically
- Simple: `hwml build` just works

### Phase 2: Workspaces
- Add `hwml-workspace.toml`
- Multiple libraries in one repo
- Shared dependencies
- LSP understands workspace

### Phase 3: Multiple Build Configs
- Add `builds/*.toml`
- Different targets (FPGA, ASIC, sim)
- Different profiles (dev, release, ci)
- Switch builds: `hwml use-build`

### Phase 4: Buck2/Nix (Enterprise)
- Generate Buck2/Nix from `hwml.toml`
- Leverage their remote execution
- Integrate with large monorepos
- Advanced caching strategies

---

## Open Questions

1. **Build config file naming:**
   - `hwml-build.toml` vs `hwml.build.toml` vs `build.toml`?
   - **Recommendation:** `hwml-build.toml` for clarity

2. **Workspace vs build separation:**
   - Should workspace file include default build settings?
   - **Recommendation:** Yes, for simple projects. Complex projects use separate build files.

3. **Multiple lock files:**
   - One per build config or one shared?
   - **Recommendation:** One shared, solver considers all features/targets

4. **Registry format:**
   - Git repos, tarball index, or custom format?
   - **Recommendation:** Git repos initially (like Cargo before crates.io), migrate to index later

5. **Toolchain management:**
   - Download/manage hwml/circt versions automatically?
   - **Recommendation:** Yes, similar to rustup. `hwml toolchain install 0.3.0`

---

## Success Metrics

- [ ] Library authors only edit `hwml.toml`
- [ ] LSP finds build context within 5 seconds
- [ ] Build switching (`hwml use-build`) takes <1 second
- [ ] Buck2 integration tested on 100+ library monorepo
- [ ] Nix integration produces bit-identical builds
- [ ] Local development across workspaces works seamlessly
- [ ] Remote execution enabled with single config flag
- [ ] Lock file conflicts resolvable automatically >90% of time

---

## References

**Related ADRs and Research:**
- [[ADR-004-mvs-package-manager]] - MVS dependency resolution
- [[research/modern-build-systems]] - Buck2, Nix, Bazel systems
- [[research/buck2-integration-patterns]] - Compiler architecture for Buck2 integration
- [[research/build-system-caching-synthesis]] - Caching strategies and persistent workers
- [[research/incremental-compilation-synthesis]] - Caching, remote execution
- [[research/content-addressable-storage-systems]] - CAS implementations

**External Documentation:**
- Cargo Book: https://doc.rust-lang.org/cargo/
- Buck2 Documentation: https://buck2.build/docs
- Buck2 Persistent Workers: https://buck2.build/docs/rule_authors/persistent_workers/
- Nix Manual: https://nixos.org/manual/nix/
- Bazel Remote Execution API: https://github.com/bazelbuild/remote-apis

---

---

## Implementation Phases

### Phase 1: Basic Workspace Support
**Goal:** Multi-file libraries with basic dependency management

**Tasks:**
- [ ] `hwml-workspace` crate: manifest parsing, topo-sort, file discovery
- [ ] `SourceInfo::File(SourceFileId)` replacing current `File(Word)`
- [ ] Thread `Source` through elaborator; attach `SourceRange` to declarations
- [ ] `.hwmli` serialization/deserialization (full elaborated AST + import table)
- [ ] Per-project cache (`.hwml-build/`)
- [ ] `open` statement elaboration (basic: bring library names into scope)
- [ ] CLI: `hwml build [--manifest hwml.toml]`

**Deliverables:**
- Multiple `.hwml` files can form a library
- Libraries can depend on other libraries (path deps only)
- Artifacts cached in `.hwml-build/`

---

### Phase 2: User-Global Cache
**Goal:** Share artifacts across projects on one machine

**Tasks:**
- [ ] `~/.cache/hwml/cas/` store with git-style sharding
- [ ] Content-addressable storage (BLAKE3 hashing)
- [ ] Hardlink from CAS into project `.hwml-build/` on cache hit
- [ ] `hwml gc` to prune unreferenced cache entries
- [ ] `hwml build --reproducibility-check` (build twice, compare)

**Deliverables:**
- Artifacts shared across multiple projects
- Faster clean builds (cache hits from other projects)
- Reproducible builds verified

---

### Phase 3: Package Manager + Lock Files
**Goal:** Registry-based dependencies with version resolution

**Tasks:**
- [ ] `hwml.lock` format (MVS resolution output)
- [ ] MVS solver implementation
- [ ] `hwml install`, `hwml update <package>`
- [ ] Registry support (initially: Git repos, like Go modules)
- [ ] Breaking change versioning (`my-lib/v2` import paths)

**Deliverables:**
- External dependencies from registry
- Reproducible dependency resolution
- Lock file committed to VCS

---

### Phase 4: Build Configuration Layer
**Goal:** Separate build settings from library manifests

**Tasks:**
- [ ] `hwml-workspace.toml` format
- [ ] `hwml-build.toml` and `builds/*.toml` support
- [ ] Build profiles (dev, release, ci)
- [ ] Feature flags and conditional compilation
- [ ] Target configuration (FPGA, ASIC, simulation)
- [ ] LSP build discovery (`.hwml/active-build.toml`)
- [ ] CLI: `hwml use-build builds/fpga.toml`

**Deliverables:**
- Multiple build configurations from same codebase
- LSP uses correct build context
- Build engineers control settings separately from library authors

---

### Phase 5: Remote Cache + Early Cutoff
**Goal:** Team-wide artifact sharing and fine-grained incremental compilation

**Tasks:**
- [ ] REapi v2 client (BuildBarn, BuildBuddy compatible)
- [ ] Remote read/write with authentication
- [ ] Per-declaration fingerprints (GHC-style)
- [ ] Usage tracking (which declarations were actually used)
- [ ] Early cutoff (skip recompilation if used declarations unchanged)
- [ ] `[cache]` section in build files for remote endpoint config

**Deliverables:**
- Artifacts shared across team and CI
- Fine-grained incremental compilation
- Reduced CI build times

---

### Phase 6: External Build System Integration
**Goal:** Integration with Buck2, Nix, and other build systems

**Tasks:**
- [ ] `hwml generate buck` (generate `BUCK` files from `hwml.toml`)
- [ ] `hwml generate nix` (generate Nix derivations)
- [ ] Buck2 `hwml_library()` rule implementation
- [ ] Nix `buildHwmlLibrary` function
- [ ] Documentation and examples

**Deliverables:**
- Buck2 orchestrates HWML builds in monorepo
- Nix provides hermetic release builds
- Both leverage HWML's native caching

---

**Status:** Proposed
**Next Steps:**
1. Review ADR-006 with core team
2. Reconcile with `design/package-manager.md` (see `wiki/analysis/ADR-006-vs-package-manager-design-reconciliation.md`)
3. Begin Phase 1 implementation: `hwml-workspace` crate
4. Create proof-of-concept manifest parser
5. Design `.hwmli` serialization format
