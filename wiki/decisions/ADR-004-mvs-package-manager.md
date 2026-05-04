# ADR-004: Minimum Version Selection for Package Manager

**Status:** Approved (Implementation: Phase 3)  
**Date:** 2026-03-15  
**Phase:** Phase 3 (Planned)  
**Confidence:** 0.95

---

## Context

HWML needs a package manager to handle library dependencies. As a hardware description language where reproducibility is critical, we must choose a dependency resolution strategy that prioritizes deterministic, reproducible builds over finding the "latest compatible" versions.

**Requirements:**
- Reproducible builds across machines and time
- No silent version downgrades
- Simple mental model for users
- Deterministic resolution (no solver complexity)

---

## Alternatives Considered

### Option 1: SemVer with SAT Solver (npm, Cargo style)
Use semantic versioning with a constraint solver to find "best" compatible versions.

**Pros:**
- Flexible - finds newest compatible versions
- Users get bug fixes automatically
- Industry standard (npm, Cargo, pip)

**Cons:**
- **Non-deterministic** - Different machines/times may get different versions
- **Silent downgrades** - Adding dep X might downgrade dep Y
- **Complex** - SAT solver is non-trivial code
- **Surprising** - Version resolution can be hard to predict

**Verdict:** **Rejected** - Non-determinism is unacceptable for hardware

### Option 2: Minimum Version Selection (Go, Zig style)
For each package, take the **maximum** of all minimum version requirements across the dependency graph.

**Pros:**
- **Deterministic** - Same graph always resolves to same versions
- **Simple** - No solver, straightforward algorithm
- **Reproducible** - Build today = build tomorrow = build on other machine
- **Explicit upgrades** - User runs `hwml update` to get newer versions
- **No downgrades** - Adding a dependency never lowers another's version

**Cons:**
- Won't automatically use latest compatible versions
- Security patches require explicit `hwml update`
- Doesn't find "optimal" version set (but what is optimal?)

**Verdict:** **Chosen** - Reproducibility matches HWML's needs perfectly

### Option 3: Lock Everything (Pure lockfile, no ranges)
Require exact versions in `hwml.toml`, no version ranges.

**Pros:**
- Maximum explicitness
- Zero ambiguity

**Cons:**
- Poor UX - every version bump requires manual edit
- Doesn't compose - two libraries can't both depend on "lib v1.2"
- Overly rigid

**Verdict:** **Too extreme** - Version ranges are useful

### Option 4: Manual Vendoring
No package manager - users manually copy dependencies.

**Pros:**
- Complete control
- No dependency on external infrastructure

**Cons:**
- Manual maintenance burden
- No version management
- Hard to update dependencies
- Doesn't scale

**Verdict:** **Not sustainable** for ecosystem growth

---

## Decision

Use **Minimum Version Selection (MVS)** as designed by Russ Cox for Go modules.

### How MVS Works

Given dependency graph with version requirements:

```
Root depends on:
  - A >= 1.2
  - B >= 1.0

A-1.2 depends on:
  - C >= 1.1

B-1.0 depends on:
  - C >= 1.3
```

**MVS Resolution:**
1. Walk the full dependency graph
2. For each package, collect all minimum version requirements
3. Take the **maximum** of those minimums
4. Result: `A=1.2, B=1.0, C=1.3`

**Key property:** Always deterministic. Same graph → same resolution.

### Version Declaration

In `hwml.toml`:
```toml
[dependencies]
hwml-prelude = "^1.0"      # Human-readable range (1.x compatible)
some-lib = { path = "../local-lib" }
```

In `hwml.lock`:
```toml
[[package]]
name = "hwml-prelude"
version = "1.3.2"                        # Exact resolved version
source_hash = "sha256:abc123..."         # Content hash (identity)
url = "https://packages.hwml.dev/..."   # Hint (not identity)
```

**Critical:** Hash is identity, URL is hint. Any mirror with matching hash is valid.

---

## Rationale

### Why MVS for HWML?

1. **Hardware compilation demands reproducibility**
   - A circuit that works today must work tomorrow
   - Different machines must produce identical results
   - No "it works on my machine" for hardware

2. **Determinism over convenience**
   - We prefer explicit `hwml update` over automatic version bumps
   - Users know exactly what versions they're getting
   - No surprises in CI vs local builds

3. **Simpler implementation**
   - No SAT solver required (~3000 lines of complex code saved)
   - Easy to understand, audit, and maintain
   - Faster resolution (no backtracking)

4. **Go and Zig prove it works**
   - Go modules have used MVS successfully since 2019
   - Zig package manager uses similar approach
   - Both prioritize reproducibility over "latest versions"

### Handling Breaking Changes

**Go-style major versioning:** Breaking changes use new import path.

```hwml
import my-lib      -- v1.x
import my-lib/v2   -- v2.x (breaking changes)
```

Both versions can coexist in one build. No diamond dependency type conflicts.

---

## Implementation

**Crate:** `hwml-workspace` (new)

**Algorithm:**
```rust
pub fn resolve_mvs(root: &LibraryManifest) -> Result<HashMap<String, Version>> {
    let mut required: HashMap<String, Version> = HashMap::new();
    
    fn walk(lib: &LibraryManifest, required: &mut HashMap<String, Version>) {
        for dep in &lib.dependencies {
            // Take maximum of current and new requirement
            required.entry(dep.name.clone())
                .and_modify(|v| *v = v.max(dep.min_version))
                .or_insert(dep.min_version);
                
            // Recursively walk this dependency
            let dep_lib = load_library(&dep);
            walk(dep_lib, required);
        }
    }
    
    walk(root, &mut required);
    Ok(required)
}
```

**Commands:**
- `hwml build` - Uses locked versions from `hwml.lock`
- `hwml update` - Recomputes MVS, updates lock file
- `hwml update <package>` - Updates specific package to newest compatible

---

## Consequences

### Positive
✅ **Reproducibility** - Builds are byte-identical across machines  
✅ **Determinism** - No surprises in version resolution  
✅ **Simplicity** - Easy to understand and predict  
✅ **No downgrades** - Adding dep X never lowers dep Y's version  
✅ **Explicit control** - User decides when to update  
✅ **Fast resolution** - No backtracking, no solver

### Negative
❌ **Manual security patches** - Won't auto-update for CVE fixes  
❌ **Not "optimal"** - Might not use newest compatible versions  
❌ **Requires discipline** - Users must remember to update

### Trade-offs

We chose:
- **Reproducibility over automatic updates**
- **Determinism over "optimal" versions**
- **Explicit control over convenience**
- **Simple implementation over complex solver**

**For hardware design, this is the right trade-off.** Synthesis tools don't auto-update either.

---

## Comparison with Cargo

| Aspect | Cargo (Rust) | HWML (MVS) |
|--------|--------------|------------|
| Resolution | SAT solver | Maximum of minimums |
| Determinism | Lock file only | Algorithm + lock file |
| Updates | `cargo update` flexible | `hwml update` deterministic |
| Downgrades | Possible (silent) | Never |
| Breaking changes | Major version | New import path |

Cargo prioritizes "latest compatible." HWML prioritizes "reproducible."

---

## Sources

**Primary Design Document:**
- `design/package-manager.md` (Part 1: Library System)

**Research:**
- Russ Cox: ["Minimal Version Selection"](https://research.swtch.com/vgo-mvs) (2018)
- Go Modules design
- Zig package manager design
- Nix package manager (for content-addressing ideas)

**Discussions:**
- Design review: 2026-03-10
- Consensus: Reproducibility is critical for hardware

---

## Related

**Decisions:**
- [[ADR-005-content-addressed-artifacts]] - Hash-based storage for packages
- [[ADR-006-hwmli-format]] - Compilation artifacts

**Entities:**
- [[entities/mvs]] - Detailed MVS algorithm explanation
- [[entities/content-addressed-storage]] - How hashes ensure reproducibility

**Components:**
- [[components/package-manager]] - Full package manager implementation

**Implementation:**
- **Phase:** 3 (Planned)
- **Crate:** `hwml-workspace`
- **Dependencies:** `petgraph` (graph algorithms), `toml` (manifest parsing)

---

## Open Questions

- [ ] **Registry protocol:** Use GitHub-based (like Reservoir) or custom?
- [ ] **Private packages:** Authentication mechanism?
- [ ] **Monorepo support:** How to handle workspace with multiple libraries?

---

## Status History

- **2026-03-10:** MVS vs SAT solver discussion
- **2026-03-15:** Decision approved (this ADR written)
- **Phase 3:** Implementation planned (not yet started)
