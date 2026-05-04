# ADR-006 vs Package Manager Design - Reconciliation Analysis

**Date:** 2026-05-03  
**Purpose:** Compare and reconcile `ADR-006-multi-layer-build-configuration.md` with `design/package-manager.md`

---

## Executive Summary

**ADR-006** proposes a multi-layer build configuration system (manifest + build + lock). 

**`design/package-manager.md`** is an earlier design covering library system, manifests, lock files, and compilation cache.

**Overall:** The two documents are **complementary and mostly aligned**, but ADR-006 adds explicit separation of build configuration from library manifests. Some details need to be merged.

---

## Areas of Agreement ✅

| Aspect | Both Documents Agree |
|--------|---------------------|
| **Per-library manifest** | `hwml.toml` in each library root |
| **Lock file** | Auto-generated `hwml.lock`, committed to VCS |
| **MVS resolution** | Minimum Version Selection for dependencies |
| **Path dependencies** | `path = "../local-lib"` for local dev |
| **Registry dependencies** | Version + content hash for external packages |
| **Workspace concept** | Multiple libraries in one workspace |
| **`.hwmli` artifacts** | Compiled elaborated AST format |
| **Cache tiers** | Project local → user global → remote |
| **Remote cache** | REapi v2 protocol (BuildBarn, BuildBuddy) |
| **Nix/Buck2 integration** | External build system orchestration |

---

## Key Differences & Reconciliation

### 1. **Workspace File**

| Document | Approach |
|----------|----------|
| `design/package-manager.md` | Workspace inferred from dependency graph |
| **ADR-006** | Explicit `hwml-workspace.toml` with `[workspace]` section |

**Reconciliation:** ADR-006 is more explicit and follows Cargo's model. Adopt `hwml-workspace.toml` for clarity.

---

### 2. **Build Configuration**

| Document | Approach |
|----------|----------|
| `design/package-manager.md` | Cache config in `hwml.toml` |
| **ADR-006** | Separate `hwml-build.toml` or `builds/*.toml` |

**Reconciliation:** ADR-006 correctly separates build settings (target, optimization, cache) from library metadata. **Adopt ADR-006 approach.**

**Rationale:**
- Library authors shouldn't specify cache URLs (build-specific)
- Same library can build for FPGA vs ASIC (different configs)
- Build engineers control optimization, remote execution

---

### 3. **Manifest Section Name: `[library]` vs `[package]`**

| Document | Section Name |
|----------|-------------|
| `design/package-manager.md` | `[library]` |
| **ADR-006** | `[package]` |

**Reconciliation:** **Use `[package]`** (ADR-006 is correct).

**Rationale:**
- Packages have versions; libraries are the code
- Aligns with Cargo, npm, Go modules
- `hwml.lock` already uses `[[package]]`
- Clearer terminology for registry publication

---

### 4. **Source File Ordering** ⚠️

**`design/package-manager.md` includes:**
```toml
[sources]
files = ["types.hwml", "defs.hwml"]
```

**ADR-006:** Does not mention this.

**Reconciliation:** **Add `[sources]` section to ADR-006**.

**Rationale:**
- Elaboration order matters for forward references
- Default: alphabetical glob of `*.hwml`
- Explicit control when needed
- Future: two-pass elaboration removes this constraint

**Recommended addition to ADR-006 manifest:**
```toml
[package]
name = "uart-controller"
version = "0.2.1"

# Optional: control elaboration order
[sources]
files = ["types.hwml", "impl.hwml", "tests.hwml"]
# If omitted, alphabetical glob of *.hwml files

[lib]
path = "src/lib.hwml"  # Library entry point

[[bin]]
name = "uart-testbench"
path = "tests/tb_uart.hwml"
```

---

### 5. **Build Profiles**

| Document | Coverage |
|----------|----------|
| `design/package-manager.md` | Not mentioned |
| **ADR-006** | Explicit profiles (dev, release, ci) |

**Reconciliation:** **Add to final design** (ADR-006 is more complete).

---

### 6. **Features System**

| Document | Coverage |
|----------|----------|
| `design/package-manager.md` | Not detailed |
| **ADR-006** | Cargo-style features with optional deps |

**Reconciliation:** **Adopt ADR-006 features system**.

---

### 7. **LSP Build Discovery**

| Document | Approach |
|----------|----------|
| `design/package-manager.md` | `Workspace::find_manifest()` walks up from current file |
| **ADR-006** | Workspace root + `.hwml/active-build.toml` for build selection |

**Reconciliation:** **Combine both**:
1. LSP walks up to find `hwml-workspace.toml` (from `design/package-manager.md`)
2. Reads `.hwml/active-build.toml` to select active build config (from ADR-006)
3. Falls back to default build if no active selection

---

## Missing from ADR-006 (Should Add)

1. **`[sources]` section** for elaboration order control
2. **`[lib]` and `[[bin]]` sections** to distinguish library code from testbenches
3. **Implementation phases** (ADR-006 has migration path, but not implementation phases like `design/package-manager.md`)
4. **`hwml-workspace` crate design** (Rust API from `design/package-manager.md`)

---

## Missing from `design/package-manager.md` (ADR-006 Adds)

1. ✅ Explicit workspace file (`hwml-workspace.toml`)
2. ✅ Separate build configuration files
3. ✅ Multiple build configurations (FPGA, ASIC, sim)
4. ✅ Build profiles (dev, release, ci)
5. ✅ LSP build selection mechanism
6. ✅ Path overrides for cross-workspace development
7. ✅ Buck2/Nix generator tools (`hwml generate buck`, `hwml generate nix`)
8. ✅ Target platform configuration

---

## Recommended Unified Manifest Schema

```toml
# Library metadata
[package]
name = "uart-controller"
version = "0.2.1"
authors = ["Your Name <you@example.com>"]
license = "MIT OR Apache-2.0"
description = "Configurable UART controller"
edition = "2026"

# Source file elaboration order (optional)
[sources]
files = ["types.hwml", "impl.hwml"]
# If omitted: alphabetical glob of *.hwml

# Entry points
[lib]
path = "src/lib.hwml"

[[bin]]
name = "uart-testbench"
path = "tests/tb_uart.hwml"

# Dependencies
[dependencies]
fifo = { path = "../fifo" }
std = "1.4.2"

[dev-dependencies]
simulation-utils = "0.1"

# Features
[features]
default = ["fifo-overflow-protection"]
debug-ports = []
fifo-overflow-protection = ["fifo/overflow-checks"]
```

---

## Action Items

- [ ] Update ADR-006 to include `[sources]`, `[lib]`, `[[bin]]` sections
- [ ] Standardize on `[package]` terminology throughout
- [ ] Add `hwml-workspace` crate API design to ADR-006 or separate ADR
- [ ] Clarify LSP discovery algorithm (combine both approaches)
- [ ] Update wiki index to reflect both documents
- [ ] Consider merging `design/package-manager.md` content into wiki (it's comprehensive!)

---

## Conclusion

**ADR-006** is the correct strategic direction:
- ✅ Separates library concerns from build concerns
- ✅ Enables multiple build configurations
- ✅ Better Buck2/Nix integration
- ✅ Clearer LSP build context

**`design/package-manager.md`** has critical implementation details:
- ✅ `[sources]` file ordering
- ✅ `hwml-workspace` crate API
- ✅ Implementation phases
- ✅ `.hwmli` artifact format details

**Recommendation:** Update ADR-006 with missing details from `design/package-manager.md`, then use ADR-006 as the canonical specification.
