# HWML Package Manager & Compilation Cache Design

## Overview

This document covers two related concerns:

1. **Library system**: how multiple files form a library, how libraries declare
   and resolve dependencies, how namespaces and name resolution work
   cross-library.
2. **Compilation cache**: how compiled artifacts are stored, keyed, shared, and
   invalidated — including a per-user CAS cache and optional remote shared
   cache.

Research basis: Lean 4/Lake, Agda, Coq, GHC/Cabal, OCaml/Dune, Nix, Bazel,
Buck2, sccache, Zig, Go modules.

---

## Part 1: Library System

### Core Model

A **library** is a named collection of `.hwml` source files that share a flat
namespace. Libraries depend on other libraries; the dependency graph must be
acyclic. Within a library, declarations can appear in any file — there is no
file-based namespacing. Files use `namespace` blocks to organize declarations
into qualified name prefixes, but namespace membership is purely syntactic.

This is identical to Agda's module system with the exception that Agda modules
map to files while HWML namespaces do not.

### Library Manifest (`hwml.toml`)

Every library root contains `hwml.toml`:

```toml
[library]
name = "my-hardware"
edition = 1              # language edition; bump on breaking language changes

[dependencies]
hwml-prelude = "^1.0"
some-lib = { path = "../local-lib" }   # local path dep
# future: registry deps automatically resolved

# Optional. Controls elaboration order within the library.
# Defaults to alphabetical glob of all *.hwml files in the library root.
[sources]
files = ["types.hwml", "defs.hwml"]
```

**Source file ordering** controls elaboration order within a library. When
`[sources]` is absent, all `.hwml` files in the library root are discovered
alphabetically. Forward references between files require that the declaring file
appear earlier in the list.

Future: a two-pass elaboration (collect type signatures first, then elaborate
bodies) would eliminate ordering constraints and enable mutual recursion across
files. The two-pass approach is planned but not in scope for the initial
implementation.

### Lock File (`hwml.lock`)

`hwml.lock` is committed to VCS and pins all dependencies to exact content
hashes. Version ranges in `hwml.toml` are for human communication; the lock
file is the ground truth for reproducible builds.

```toml
[[package]]
name = "hwml-prelude"
version = "1.3.2"
source_hash = "sha256:abc123def456..."   # SHA-256 of source NAR
url = "https://packages.hwml.dev/hwml-prelude/1.3.2.tar.gz"

[[package]]
name = "some-lib"
source_hash = "sha256:789abc..."
path = "../local-lib"                    # local deps record hash too
```

Hash is identity; URL is a hint. Any mirror serving bytes that hash correctly
satisfies the dependency. This is the Zig lesson: `packages do not come from a
URL; they come from a hash`.

### Version Resolution: Minimum Version Selection

HWML uses Go's Minimum Version Selection (MVS) rather than a SAT solver:

1. Walk the full dependency graph.
2. For each package, take the maximum of all minimum version requirements across
   the graph.
3. Result is fully deterministic without a solver; adding a dependency never
   silently downgrades others.

Tradeoff: security patches are never automatically applied. Users must run
`hwml update <package>` explicitly. This is the correct tradeoff for a language
where reproducibility matters more than automatic updates.

**Breaking changes** use a new import path suffix (Go-style). `my-lib` and
`my-lib/v2` are distinct libraries that can coexist in one build without type
conflicts. This avoids SemVer diamond dependency type incompatibility.

### Name Resolution and `open`

**Within a library**: names are referenced as declared (no library prefix).
All files in the library share one namespace pool.

**Cross-library**: dependency names live under the library name as a top-level
namespace prefix. `hwml-prelude/Nat` references `Nat` from `hwml-prelude`.

```hwml
-- Bring all hwml-prelude names into scope (no prefix needed):
open hwml-prelude

-- Selective import:
open hwml-prelude only (Nat, Vec)

-- Exclusion:
open hwml-prelude hiding (Eq)

-- Rename on import:
open hwml-prelude renaming (Nat to N)

-- Without open, use fully qualified:
def foo : hwml-prelude/Nat = ...
```

Name lookup order in the elaborator:

1. Local de Bruijn context (lambda/pi binders)
2. Current namespace + enclosing namespace blocks
3. Opened namespaces (last `open` wins; two opens bringing same unqualified
   name = error, not shadowing)
4. Fully qualified global name

**Conflict on open**: error, not silent shadowing. User must alias:
`open A renaming (Foo to AFoo)`.

### Compilation Pipeline

```
hwml build [--manifest hwml.toml]

1.  Workspace::load(manifest_path)
      → read hwml.toml, recursively load transitive deps
      → detect cycles (error with cycle path)
      → topological sort: leaves first, root last

2.  for lib in topo_order:
      for file in lib.source_files (in declared order):
        parse_surface_file(file)   → SurfaceProgram
      flatten_namespaces(programs)
        → Vec<(QualifiedName, SurfaceDecl, SourceRange)>
      elab_library(decls, &global_env)
        → Vec<Declaration>
      global_env.extend(decls, lib.name)
      write_hwmli(lib, decls)

3.  CompilationUnit from root library → codegen
```

### Source Location Architecture

Every declaration produced by elaboration carries a `SourceRange`:

```rust
pub struct SourceRange<'db> {
    pub source: Source<'db>,   // identifies the file
    pub range: Range<usize>,   // byte offsets [start, end)
}

#[salsa::interned]
pub struct SourceFileId {
    pub library_name: Word<'db>,    // interned library name string
    pub canonical_path: Word<'db>,  // interned absolute canonical path
}

pub enum SourceInfo<'db> {
    File(SourceFileId<'db>),   // replaces current File(Word<'db>)
    Synthetic(Word<'db>),
}
```

Line/column conversion is lazy and done at display time:

```rust
fn format_location(db: &dyn Database, sr: &SourceRange) -> String {
    // SourceInfo::File(id) → canonical path string
    // Load file contents, build LineInfo, convert offset → (line, col)
    "library/path/to/file.hwml:12:5"
}
```

For LSP jump-to-definition, `SourceRange` → LSP `Location` via the same path.
`hwml-support::LineInfo` already provides `offset_to_line_col`; it just needs
to be wired in.

**Requirement**: `SourceRange` must be attached to every declaration during
elaboration. Currently all spans are `None`. The current `Source` (file ID)
must be threaded into `Kernel` or `Elaborator` and applied to each elaborated
declaration.

---

## Part 2: Compilation Cache

### Why We Need a Cache

Dependently-typed elaboration is expensive. Importing a library requires loading
its full elaborated terms (types + values) — not just type signatures — because
downstream elaboration may need to reduce upstream definitions. This is
unavoidable for dependent types; both Lean 4 and Agda learned this.

Without a cache, every `hwml build` re-elaborates all transitive dependencies
from source. For large dependency graphs this is prohibitively slow.

### Artifact Format: `.hwmli`

One `.hwmli` file per library (not per source file). Stores the full elaborated
IR of all declarations in the library.

```
.hwmli binary format:

Header (fixed-size):
  magic:           [0x68 0x77 0x6d 0x6c 0x69]  "hwmli"
  format_version:  u8     (bump on breaking format change, not compiler change)
  compiler_hash:   [u8; 32]  SHA-256 of hwml compiler binary
  edition:         u32

Import table:
  count: u32
  entries: [(library_name: str, export_interface_hash: [u8; 32])]
    -- export_interface_hash = hash of exported decl types only (not bodies)
    -- checked at load time; mismatch = error with clear message

Per-declaration fingerprints:
  HashMap<QualifiedName, [u8; 32]>
    -- GHC-style: per-declaration hash of (type + value + transitive deps used)
    -- enables fine-grained early cutoff (see below)

Export interface hash:
  [u8; 32]  -- hash of all exported decl types (not bodies)
            -- = the value stored in importers' import tables

Body (zstd-compressed):
  declarations: Vec<Declaration>   -- full elaborated AST, types + values
  source_ranges: HashMap<QualifiedName, SourceRange>  -- for error reporting
```

**Consistency check on load**: when loading a `.hwmli`, each entry in the
import table is checked against the `export_interface_hash` of the currently
available artifact for that library. A mismatch produces an error analogous to
OCaml's `"inconsistent assumptions over interface X"`. This correctness
guarantee survives manual file copies, race conditions, and build system bypasses.

**Compiler hash**: any compiler version change invalidates all cached artifacts
automatically. No separate version field; the compiler binary content is the
version.

### Cache Key

```
cache_key = SHA-256(
    compiler_hash,                        // SHA-256 of hwml binary
    edition: u32,
    sorted(source_file_content_hashes),   // sorted by path; hash content not path
    sorted(dep_export_interface_hashes),  // direct deps only; transitivity is
                                          // captured by dep's own key
    normalized_flags,                     // sorted; strip debug/trace flags
)
```

Key properties:
- Hash **content**, not paths. Two machines with different source trees but
  identical content share the same cache key.
- Hash dep **interfaces** (exported types), not dep **artifacts** (full bodies).
  If a dep's implementation changes but its exports don't, the downstream cache
  key is unchanged. This is early cutoff.
- Normalize flags: debug flags that don't affect elaboration are excluded from
  the key to avoid spurious cache misses.

### Early Cutoff via Per-Declaration Fingerprints

GHC's recompilation avoidance (the most sophisticated in the ecosystem):

When elaborating library B which imports library A:

1. Record which declarations from A were actually used (consulted during
   elaboration of B), along with their fingerprints at that time.
2. Store this usage list in B's `.hwmli`.
3. On next build: if A's declarations changed but B's usage list still matches
   the current fingerprints of the declarations B actually used, B does not
   need to be re-elaborated.

This avoids the Agda problem: any change to A's source causes all importers to
recompile, even if the change was to an internal helper that no importer
references. Per-declaration fingerprints break this cascade.

### Storage Tiers

```
Tier 1 — Project local:   ./.hwml-build/
  Purpose:   fast incremental builds within one project
  Structure: .hwml-build/<library-name>-<short-hash>.hwmli
  Lifetime:  disposable, rebuilt on demand
  Owner:     project

Tier 2 — Per-user global: ${XDG_CACHE_HOME:-~/.cache}/hwml/cas/
  Purpose:   share artifacts across multiple projects on one machine
  Structure: cas/<first-2-hex>/<remaining-62-hex>  (git-style)
             (hardlinked into project's .hwml-build/ on cache hit)
  Lifetime:  GC when no project references entry
  Owner:     user

Tier 3 — Remote shared:   REapi-compatible endpoint (optional)
  Purpose:   share across CI machines and team members
  Contents:  same blobs as Tier 2
  Protocol:  build.bazel.remote.execution.v2 (standard; works with BuildBarn,
             BuildBuddy, EngFlow, or any compliant server)
  Security:  write access restricted to authenticated CI; read open
  Owner:     team/org
```

Tier 2 uses hardlinks where supported (same filesystem). Zero-copy sharing
between projects that depend on the same library at the same version. Dune
uses this approach and it works well in practice.

### Relationship to Salsa

We already use Salsa for in-process incremental computation. These two layers
are complementary, not competing:

| Layer | Scope | Persistence | Mechanism |
|---|---|---|---|
| Salsa | In-process, per session | RAM only | Memoized queries, early cutoff on value equality |
| `.hwmli` cache | Cross-invocation, cross-machine | Disk / remote | CAS keyed by content hash |

Design them together: Salsa `#[salsa::tracked]` elaboration queries produce
outputs that are serialized to `.hwmli` on session exit. On cold start, load
`.hwmli` from cache and populate Salsa's memo table directly. The Salsa
early-cutoff semantics (if output value unchanged, downstream not re-evaluated)
mirror the per-declaration fingerprint logic — implement them from the same
comparison.

Buck2's DICE engine has the same relationship: in-process memoization (DICE)
plus remote CAS. They share invalidation logic. We should do the same.

### Reproducible Builds

Requirements for byte-identical output on any machine given identical inputs:

- Source file paths must not appear in `.hwmli` bodies. `SourceRange` stores
  paths for error reporting but they must not affect elaboration output.
- No timestamps embedded in artifacts.
- Compiler identity = SHA-256 of compiler binary, not version string. Two
  builds with same version string but locally patched compiler get different
  hashes.
- All inputs sorted before hashing (declaration order within a file is
  significant and preserved; but file *discovery* order from globbing must be
  deterministic = alphabetical).
- No ambient system library leakage (pure Rust compiler helps; no FFI during
  elaboration).

Verification command:
```
hwml build --reproducibility-check
  # Builds twice with identical inputs, diffs outputs.
  # CI fails if not byte-identical.
```

---

## Part 3: Package Installation

### Install Locations

```
hwml install hwml-prelude           # per-user: $XDG_DATA_HOME/hwml/packages/
hwml install --global hwml-prelude  # system-wide: /usr/local/share/hwml/
hwml install --project              # vendored: ./hwml-packages/
```

Installed packages are stored as:
- Immutable source tarballs: `<store>/<name>-<source-hash>.tar.zst`
- Extracted source: `<store>/<name>-<source-hash>/src/`
- Compiled artifacts: in the CAS cache (Tier 2 above), keyed by `cache_key`

Multiple versions of the same library coexist without conflict (Cabal-style
content-addressed store). No concept of a "switch" or "sandbox" is needed at
the package level — per-project dependency resolution handles isolation.

### Nix Integration

Nix is the right tool for **toolchain pinning and reproducible dev
environments**, not for per-library compilation caching (wrong granularity;
see analysis below).

Ship a `flake.nix` in the HWML repo:

```nix
{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  outputs = { self, nixpkgs }: {
    devShells.default = pkgs.mkShell {
      packages = [ self.packages.x86_64-linux.hwml pkgs.rust-analyzer ];
    };
    # Optional: one Nix derivation per library for fully hermetic release builds
    lib.buildHwmlLibrary = { name, src, dependencies ? [] }:
      pkgs.stdenv.mkDerivation { ... };
  };
}
```

`nix develop` gives contributors an exact-version dev environment.
`buildHwmlLibrary` is optional — for users who want fully auditable Nix-managed
release artifacts. Day-to-day development uses the native cache tiers.

**Why Nix is wrong for per-library caching**: Nix's atomic unit is the
derivation = whole package. Input-addressed paths (the current default) mean
that changing any input changes the output path, forcing downstream rebuilds
even if the elaborated output is identical. The experimental content-addressed
derivations (RFC 0062) would fix this, but are not production-ready as of 2025.
More fundamentally, Nix has no concept of "the elaborated output of this
library is an input to the elaboration of that library" — you would be
re-implementing a build system inside Nix.

---

## Part 4: New Crate — `hwml-workspace`

Owns manifest parsing, dependency graph, and topological sort. Does not depend
on `hwml-core` or `hwml-elab`.

```rust
pub struct LibraryManifest {
    pub name: String,
    pub edition: u32,
    pub root: PathBuf,               // canonical absolute path
    pub source_files: Vec<PathBuf>,  // relative to root, elaboration order
    pub dependencies: Vec<LibraryDep>,
}

pub struct LibraryDep {
    pub name: String,
    pub version_req: semver::VersionReq,   // for human display only
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

Crate dependency graph additions:

```
hwml-workspace (new)
  → toml            (manifest parsing)
  → petgraph        (topo-sort, cycle detection)
  ← hwml            (CLI uses it)
  ← hwml-lsp-server (workspace open, file watching)

hwml-db
  → hwml-workspace  (LibraryManifest as Salsa input)
  → hwml-surface    (parse_surface_file)
```

---

## Part 5: IR Changes Required

### `hwml-core`: `SourceInfo` update

Replace `SourceInfo::File(Word<'db>)` with `SourceFileId`:

```rust
// In hwml-core/src/source_range.rs:

#[salsa::interned]
pub struct SourceFileId {
    pub library_name: Word<'db>,
    pub canonical_path: Word<'db>,
}

pub enum SourceInfo<'db> {
    File(SourceFileId<'db>),   // was: File(Word<'db>)
    Synthetic(Word<'db>),
}
```

### `hwml-core`: `GlobalEnv` entry

```rust
pub struct GlobalEntry<'db> {
    pub decl: Declaration<'db>,
    pub source: Option<SourceRange<'db>>,  // definition site
    pub library: Option<String>,           // None = builtin
}
```

### `hwml-elab`: Thread `Source` through elaboration

Add `current_source: Source<'db>` to `Kernel`. Every declaration produced by
`elab_constant` and `elab_inductive` gets a `SourceRange` from
`def.loc`/`ind.name.loc` via the current source.

---

## Part 6: Lessons from Existing Systems

Failure modes to avoid:

| Footgun | System | Our mitigation |
|---|---|---|
| Non-cryptographic cache keys | Lean 4 (UInt64 hash) | SHA-256 or BLAKE3 throughout |
| No integrity check on downloaded artifacts | Lean 4 barrels | Verify all downloads against `hwml.lock` hash |
| Toolchain version auto-mutated on dep update | Lean 4 `lake update` | Never mutate pinned toolchain without explicit flag |
| Unsigned shared remote cache | sccache | Restrict write access to CI; or sign artifacts with a key |
| Stale cache undetected on compiler upgrade | Coq `.vo` | Compiler hash embedded in `.hwmli` header, checked at load |
| Any source change causes all importers to recompile | Agda `.agdai` | Per-declaration fingerprints + usage lists (GHC model) |
| TH/plugin side-effects invisible to fingerprints | GHC | No compile-time IO; elaboration must be pure and deterministic |
| Diamond deps produce multiple copies | Nix flakes | MVS: one version per library; breaking changes = new import path |
| Same bytes, different CID | IPFS | One canonical hash per content (no chunking variation) |
| Force-push invalidates pinned git SHA | Lean 4 manifests | Pin source content hash, not git SHA |

---

## Implementation Phases

### Phase 1: Multi-file + `.hwmli` format
- `hwml-workspace` crate: manifest parsing, topo-sort, file discovery
- `SourceInfo::File(SourceFileId)` replacing current `File(Word)`
- Thread `Source` through elaborator; attach `SourceRange` to all declarations
- `.hwmli` serialization/deserialization (full elaborated AST + import table)
- Per-project cache (`.hwml-build/`)
- `Open` statement elaboration (basic: bring library names into scope)

### Phase 2: Per-user CAS cache
- `~/.cache/hwml/cas/` store with git-style sharding
- Hardlink from CAS into project `.hwml-build/` on cache hit
- `hwml gc` to prune unreferenced cache entries
- `hwml build --reproducibility-check`

### Phase 3: Package manager
- `hwml.lock` format
- MVS version resolution
- `hwml install` (per-user, global, project)
- `hwml update <package>`
- Package registry (initially: GitHub-based, like Reservoir)

### Phase 4: Remote cache
- REapi client (read/write to BuildBarn or compatible server)
- `[cache]` section in `hwml.toml` for remote endpoint config
- Per-declaration fingerprints + usage lists (full GHC-style early cutoff)

### Phase 5: Ecosystem
- `nix develop` flake
- `buildHwmlLibrary` Nix derivation
- `hwml build --reproducibility-check` in CI template
