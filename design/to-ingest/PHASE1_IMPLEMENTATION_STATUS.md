# Phase 1 Implementation Status Report

## Overview
This document provides a comprehensive assessment of Phase 1 implementation progress for the HWML package manager, based on the design document `design/package-manager.md`.

## Phase 1 Requirements (from design doc)
Phase 1 includes:
- `hwml-workspace` crate: manifest parsing, topo-sort, file discovery
- `SourceInfo::File(SourceFileId)` replacing current `File(Word)`
- Thread `Source` through elaborator; attach `SourceRange` to all declarations
- `.hwmli` serialization/deserialization (full elaborated AST + import table)
- Per-project cache (`.hwml-build/`)
- `Open` statement elaboration (basic: bring library names into scope)

---

## ✅ COMPLETED Components

### 1. `hwml-workspace` Crate (COMPLETE)
**Location**: `crates/hwml-workspace/`

**Implemented Features**:
- ✅ Manifest parsing (`hwml.toml`)
  - `LibraryManifest` struct with name, edition, root, source_files, dependencies
  - Support for path dependencies: `{ path = "../local-lib" }`
  - Support for registry dependencies: `"^1.0"` (parsing only, not resolution)
  - Auto-discovery of `.hwml` files when `[sources]` section is absent
  - Explicit file ordering via `[sources] files = [...]`
  
- ✅ Workspace loading and dependency resolution
  - `Workspace::load()` - recursive manifest loading
  - `Workspace::find_manifest()` - Cargo-style upward search
  - Deduplication by canonical path
  - Error handling for missing manifests, cycles, duplicates

- ✅ Topological sorting
  - Uses `petgraph` for cycle detection
  - Returns libraries in dependency order (leaves first, root last)
  - Clear cycle error reporting

- ✅ Comprehensive test suite
  - Single library, multi-library, cycle detection, explicit sources

**Files**:
- `src/lib.rs` - Public API
- `src/manifest.rs` - TOML parsing and file discovery
- `src/workspace.rs` - Workspace loading and topological sort

### 2. `SourceFileId` Infrastructure (COMPLETE)
**Location**: `crates/hwml-core/src/source_range.rs`

**Implemented**:
- ✅ `SourceFileId` as salsa-interned struct
  - Contains `library_name: Word<'db>` and `canonical_path: Word<'db>`
  - Helper method `path_str()` for display
  
- ✅ `SourceInfo` enum updated
  - `File(SourceFileId<'db>)` - replaces old `File(Word<'db>)`
  - `Synthetic(Word<'db>)` - for compiler-generated code
  
- ✅ Integrated into core IR
  - Re-exported from `hwml-core::lib`
  - Used throughout source range infrastructure

### 3. `Open` Statement Elaboration (COMPLETE)
**Location**: `crates/hwml-elab/src/`

**Implemented**:
- ✅ Basic namespace opening (`open Foo`)
- ✅ Aliased opens (`open Foo as F`)
- ✅ Namespace resolution via `Resolver` and `StubTable`
- ✅ Scope management (functional style with cloning)
- ✅ Duplicate open detection
- ✅ Error reporting for:
  - Namespace not found
  - Ambiguous namespaces
  - Duplicate opens in same scope

**Not Yet Implemented** (acknowledged with error messages):
- ❌ `open Foo only (Bar, Baz)` - selective imports
- ❌ `open Foo hiding (Bar)` - exclusions
- ❌ `open Foo renaming (Bar to Baz)` - renaming imports

**Files**:
- `src/program.rs` - Statement elaboration loop
- `src/resolver.rs` - Namespace resolution logic
- `src/stub_table.rs` - Name lookup table

---

## ⚠️ PARTIALLY COMPLETE / IN PROGRESS

### 4. Threading `Source` Through Elaborator
**Status**: INFRASTRUCTURE READY, NOT YET WIRED UP

**What's Ready**:
- ✅ `SourceFileId` exists and is properly typed
- ✅ `SourceRange` infrastructure exists
- ✅ `HasSourceRange` trait for attaching ranges

**What's Missing**:
- ❌ Elaborator does not receive `Source` parameter
- ❌ All elaborated declarations currently use synthetic source
- ❌ `SourceRange` is not attached to declarations during elaboration

**Evidence** (from `crates/hwml-elab/src/program.rs:90-94`):
```rust
// TODO: Replace synthetic source with real SourceFileId when threading through the pipeline
let source = {
    let label = Word::new(db, "<synthetic>");
    Source::new(db, SourceInfo::Synthetic(label))
};
```

**What's Needed**:
1. Pass actual `SourceFileId` (from workspace manifest) to `elab_program`
2. Thread `Source` through `Elaborator::new()` and `Kernel`
3. Attach `SourceRange` to all declarations in elaboration functions
4. Update `GlobalEnv` to include `library: Option<String>` per declaration

---

## ❌ NOT STARTED

### 5. `.hwmli` Serialization/Deserialization
**Status**: NOT IMPLEMENTED

**Design Requirements** (from package-manager.md):
- Binary format with magic header `[0x68 0x77 0x6d 0x6c 0x69]` "hwmli"
- Format version (u8)
- Compiler hash (SHA-256 of hwml binary)
- Edition (u32)
- Import table with library names and export interface hashes
- Per-declaration fingerprints (HashMap<QualifiedName, [u8; 32]>)
- Export interface hash
- Zstd-compressed body with `Vec<Declaration>` and source ranges

**What Needs to Be Done**:
1. Create serialization format (likely using `serde` + custom binary format or `bincode`)
2. Implement `Declaration` serialization for all declaration types
3. Implement hash computation:
   - Per-declaration fingerprints
   - Export interface hash
   - Cache key computation
4. Implement consistency checking on load
5. Add zstd compression/decompression

**Blocking Issues**:
- `Declaration` types may not implement `Serialize`/`Deserialize`
- Need to handle Salsa-interned types during serialization
- Need to design stable representation for interned values

### 6. Per-Project Cache (`.hwml-build/`)
**Status**: NOT IMPLEMENTED

**Design Requirements**:
- Write compiled `.hwmli` files to `./.hwml-build/`
- Cache key based naming: `<library-name>-<short-hash>.hwmli`
- Integration with build command

**What Needs to Be Done**:
1. Implement cache directory creation
2. Implement cache lookup by key
3. Implement cache write after successful elaboration
4. Add `--force-rebuild` flag to ignore cache
5. Add cache invalidation logic

### 7. CLI Integration (`hwml build`)
**Status**: NOT IMPLEMENTED

**Current State**:
- CLI only supports single-file compilation: `hwml -f <file>`
- No `hwml build` command exists
- No workspace-aware compilation

**What Needs to Be Done**:
1. Add `build` subcommand to CLI
2. Integrate `Workspace::load()` and `Workspace::find_manifest()`
3. Implement multi-library elaboration loop:
   ```rust
   for lib_name in workspace.topo_order {
       let lib = &workspace.libraries[lib_name];
       // Parse all source files in order
       // Flatten namespaces
       // Elaborate library
       // Extend global environment
       // Write .hwmli
   }
   ```
4. Wire up source file paths to `SourceFileId`
5. Implement `.hwmli` caching and loading

---

## Implementation Roadmap

### To Complete Phase 1

#### Step 1: Thread Source Through Elaborator (2-3 days)
**Priority**: HIGH - Required for proper error messages

1. Update `elab_program()` signature to accept `Source` parameter
2. Update `Elaborator::new()` to store current `Source`
3. Update all elaboration functions (`elab_constant`, `elab_inductive`, etc.) to attach `SourceRange`
4. Update `GlobalEnv` to store library name with each declaration
5. Test that error messages now show proper file paths

**Files to Modify**:
- `crates/hwml-elab/src/program.rs`
- `crates/hwml-elab/src/elab/decl.rs`
- `crates/hwml-elab/src/elaborator.rs`
- `crates/hwml-elab/src/kernel.rs`
- `crates/hwml-core/src/val.rs` (GlobalEnv)

#### Step 2: Implement `.hwmli` Format (4-5 days)
**Priority**: HIGH - Core feature for Phase 1

1. Add serde derives to `Declaration` and related types
2. Design stable serialization for Salsa-interned types
3. Implement binary format writer/reader
4. Implement hash computation utilities
5. Add compression support
6. Write comprehensive tests

**New Files**:
- `crates/hwml-core/src/artifact.rs` - `.hwmli` format definition
- `crates/hwml-core/src/artifact/serialize.rs`
- `crates/hwml-core/src/artifact/hash.rs`

#### Step 3: Implement Cache Layer (2-3 days)
**Priority**: MEDIUM

1. Create `.hwml-build/` directory structure
2. Implement cache key computation
3. Implement cache lookup and write
4. Add cache validation (consistency checks)

**New Files**:
- `crates/hwml-workspace/src/cache.rs`

#### Step 4: Implement `hwml build` Command (3-4 days)
**Priority**: HIGH

1. Add `build` subcommand to CLI
2. Implement workspace discovery
3. Implement multi-library compilation pipeline
4. Wire up caching
5. Add progress reporting and error handling

**Files to Modify**:
- `crates/hwml/src/main.rs`
- Create `crates/hwml/src/build.rs`

#### Step 5: Testing and Documentation (2-3 days)
**Priority**: MEDIUM

1. Create example multi-library projects
2. Write integration tests for `hwml build`
3. Test cache invalidation scenarios
4. Document the build process
5. Update README with new commands

---

## Estimated Timeline

**Total Effort**: 13-18 days (2.5-3.5 weeks)

**Current Status**: ~40% complete
- Workspace infrastructure: ✅ 100%
- SourceFileId infrastructure: ✅ 100%
- Open statement: ✅ 80% (modifiers missing)
- Source threading: ⚠️ 10% (infrastructure only)
- .hwmli format: ❌ 0%
- Cache layer: ❌ 0%
- CLI integration: ❌ 0%

---

## Recommendations

### Immediate Next Steps (This Week)

1. **Complete Source Threading** - This is the foundation for everything else and enables proper error messages. The infrastructure is ready; just need to wire it up.

2. **Start `.hwmli` Format Design** - This is the most complex piece. Begin with:
   - Making `Declaration` serializable
   - Designing the binary format
   - Implementing basic write/read without compression

### Medium-Term (Next 2 Weeks)

3. **Implement Caching** - Once `.hwmli` format works
4. **Implement `hwml build`** - Integrate all pieces together
5. **Testing** - Create multi-library examples and test thoroughly

### What Can Wait (Phase 2+)

- Open statement modifiers (`only`, `hiding`, `renaming`)
- Per-user global cache (`~/.cache/hwml/cas/`)
- Remote cache
- GC and cache cleanup
- Reproducibility checks

---

## Questions/Blockers

1. **Declaration Serialization**: Do the core `Declaration` types need to be refactored to be serializable? Salsa-interned types may complicate this.

2. **Stable Representation**: How should we serialize `QualifiedName` and other interned types in a way that's stable across compilations?

3. **Backward Compatibility**: Should we version the `.hwmli` format from day 1, or accept breaking changes in early versions?

4. **Testing Strategy**: Should we add integration tests in a separate crate, or extend existing test suites?
