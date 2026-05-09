# HWML Frontend Roadmap: Quick Reference

**Date:** 2026-05-03  
**Full Plan:** See `wiki/FRONTEND-IMPLEMENTATION-PLAN.md`

---

## Current Status

✅ **Phase 1 Complete:**
- Core kernel with NbE (all tests passing)
- Bidirectional type checking
- Basic elaboration working
- Surface parser (LALRPOP)
- Salsa integration started
- LSP skeleton exists

❌ **Missing for Multi-File:**
- No `.hwmli` serialization
- No workspace/manifest loading
- No `open` statement implementation
- No build CLI

---

## The Plan: 5-7 Weeks to Working Multi-File + LSP

### Phase A: Multi-File Foundation (2-3 weeks)
**Deliverable:** Compile workspace with multiple libraries

**Week 1:**
- Implement `hwml.toml` manifest parsing
- Design `.hwmli` format (bincode serialization)
- Workspace loading with topo-sort

**Week 2:**
- Implement `open` statement elaboration
- Integrate with Salsa (workspace-aware queries)
- Cross-file name resolution

**Week 3:**
- `.hwmli` serialization/deserialization
- Test multi-library compilation

### Phase B: CLI Build Tool (1 week)
**Deliverable:** `hwml build` command that works

- Implement CLI with `clap`
- Basic caching (local `.hwml-build/` only)
- Pretty error messages with `codespan-reporting`

### Phase C: LSP Workspace Support (1-2 weeks)
**Deliverable:** LSP with go-to-definition, hover, completion

- Workspace discovery on LSP init
- Go-to-definition across files
- Hover showing types
- Basic completion

### Phase D: Integration & Polish (1 week)
**Deliverable:** VS Code extension + example project

- VS Code extension
- Example `uart-controller` project
- Documentation

---

## Week 1 Priorities (START HERE)

### Day 1-3: Manifest Parsing
**Files:** `crates/hwml-workspace/src/manifest.rs`

```rust
// Implement LibraryManifest::from_toml_file()
// Parse [package], [dependencies], [lib]
// Handle path dependencies
```

**Dependencies:** `toml`, `serde`, `semver`

### Day 4-5: `.hwmli` Format
**Files:** New crate `crates/hwml-artifact/`

```rust
#[derive(Serialize, Deserialize)]
pub struct Hwmli {
    pub version: u32,
    pub library_name: String,
    pub library_version: semver::Version,
    pub declarations: Vec<Declaration>,
    pub export_interface_hash: [u8; 32],
}
```

**Dependencies:** `serde`, `bincode`, `blake3`

### Day 6-7: Workspace Loading
**Files:** `crates/hwml-workspace/src/workspace.rs`

```rust
impl Workspace {
    pub fn load(root: PathBuf) -> Result<Self> {
        // 1. Find all hwml.toml files
        // 2. Build dependency graph (petgraph)
        // 3. Topological sort
        // 4. Detect cycles
    }
}
```

**Dependencies:** `petgraph`, `glob`

---

## Example: Multi-Library Project Structure

```
examples/uart-controller/
├── hwml-workspace.toml       # Optional: workspace metadata
├── lib/
│   ├── fifo/
│   │   ├── hwml.toml         # Package manifest
│   │   └── src/
│   │       ├── types.hwml
│   │       └── impl.hwml
│   └── uart/
│       ├── hwml.toml
│       └── src/
│           ├── types.hwml
│           ├── uart.hwml     # open Fifo
│           └── testbench.hwml
└── .hwml-build/              # Generated artifacts
    ├── fifo.hwmli
    └── uart.hwmli
```

**`lib/fifo/hwml.toml`:**
```toml
[package]
name = "fifo"
version = "0.1.0"

[lib]
path = "src/types.hwml"

[sources]
files = ["types.hwml", "impl.hwml"]
```

**`lib/uart/hwml.toml`:**
```toml
[package]
name = "uart"
version = "0.1.0"

[dependencies]
fifo = { path = "../fifo" }

[lib]
path = "src/uart.hwml"
```

**`lib/uart/src/uart.hwml`:**
```hwml
open Fifo

def makeUart (capacity : Nat) : Module =
    let queue = Fifo.Queue capacity in
    -- ... rest of implementation
```

---

## Success Criteria

After implementation:

- [ ] `hwml build` compiles multi-library workspaces
- [ ] `.hwmli` artifacts cached and reused
- [ ] LSP shows errors across files in VS Code
- [ ] Go-to-definition jumps across files
- [ ] Hover shows types
- [ ] Incremental builds work (only recompile changed files + dependents)

---

## Key Resources

**Full Implementation Plan:** `wiki/FRONTEND-IMPLEMENTATION-PLAN.md`

**Related Docs:**
- `design/package-manager.md` - Package manager design
- `design/to-ingest/PHASE1-COMPLETE.md` - What's complete
- `wiki/decisions/ADR-006-multi-layer-build-configuration.md` - Build config

**Current Code:**
- `crates/hwml-core/` - Kernel (working)
- `crates/hwml-elab/` - Elaborator (working)
- `crates/hwml-surface/` - Parser (working)
- `crates/hwml-workspace/` - Manifest types (stub)
- `crates/hwml-lsp-server/` - LSP skeleton (basic)
- `crates/hwml-db/` - Salsa database (basic)

---

## Next Action: Start Week 1!

```bash
cd crates/hwml-workspace
# Implement manifest parsing
# See wiki/FRONTEND-IMPLEMENTATION-PLAN.md Phase A.1 for details
```
