# VFS Implementation Plan

**Status:** Ready for Implementation
**Created:** 2026-05-04
**Related:** [[decisions/ADR-008-vfs-abstraction]], [[VFS-REVIEW-SUMMARY]]

---

## Executive Summary

This document provides a detailed implementation plan for ADR-008 (VFS Abstraction). The ADR architecture is **state-of-the-art and correct**. However, the current codebase has a critical anti-pattern where `files: DashMap` lives inside `HwmlDatabase`, violating the principle that VFS should feed Salsa inputs, not hide behind side effects.

**Critical Issue:** Current `HwmlDatabase` has `files: DashMap<PathBuf, File>` stored internally, which works for single-file CLI but will break LSP incremental compilation.

**Solution:** Implement ADR-008 exactly as specified, moving file management outside the database into a `CompilerSession` wrapper.

---

## Current vs Target Architecture

### Current (Anti-Pattern)
```rust
#[salsa::db]
pub struct HwmlDatabase {
    storage: salsa::Storage<Self>,
    files: DashMap<PathBuf, File>,  // ❌ Inside database!
    logs: Arc<Mutex<Option<Vec<String>>>>,
}

#[salsa::input]
pub struct File {
    pub text: String,  // ❌ Missing path field
}
```

**Problems:**
- No way to update file content (breaks LSP)
- File cache hidden from proper abstraction
- Direct `fs::read_to_string` in CLI code
- Tests use `tempfile` (slow, flaky)

### Target (ADR-008 Compliant)
```rust
// VFS lives OUTSIDE the database
pub struct CompilerSession {
    pub db: HwmlDatabase,
    file_cache: DashMap<PathBuf, SourceFile>,  // ✅ Outside Salsa
}

#[salsa::input]
pub struct SourceFile {
    #[return_ref]
    pub path: PathBuf,  // ✅ Has path
    
    #[return_ref]
    pub text: String,  // ✅ Updatable via set_text()
}
```

**Benefits:**
- `file.set_text(&mut db).to(new_text)` triggers Salsa invalidation
- Clean separation: Session manages files, Salsa tracks content
- Pluggable VFS implementations (OS, Memory, LSP)
- Fast, hermetic testing

---

## Implementation Phases

### Phase 1: Fix Critical Anti-Pattern (2-3 days)
**Goal:** Remove VFS from inside database, create proper separation

**Tasks:**
1. Rename `File` → `SourceFile`, add `path` field
2. Remove `files: DashMap` from `HwmlDatabase`
3. Create `CompilerSession` struct with file cache
4. Move lazy loading from `db.input()` to session
5. Add `update_file()` for LSP support

**Success Criteria:**
- ✅ No file state inside `HwmlDatabase`
- ✅ All queries take `SourceFile` parameter
- ✅ Can call `file.set_text()` to update content

### Phase 2: Implement VFS Foundation (2-3 days)
**Goal:** Create `hwml-vfs` crate with trait and basic implementations

**Tasks:**
1. Create `crates/hwml-vfs/` crate
2. Define `Vfs` trait (get_or_create_file, update_file, get_file)
3. Implement `OsVfs` (filesystem with canonicalization)
4. Implement `MemoryVfs` (HashMap-based for tests)
5. Add factory constructors to `CompilerSession`

**Success Criteria:**
- ✅ Can swap VFS implementations via trait object
- ✅ `OsVfs` reads from disk with proper path handling
- ✅ `MemoryVfs` works fully in-memory

### Phase 3: Migrate Existing Code (3-4 days)
**Goal:** Update all existing code to use new architecture

**Tasks:**
1. Update CLI `main.rs` to use `CompilerSession`
2. Change `parse_program` to take `SourceFile`
3. Migrate workspace loading to VFS
4. Update mdbook preprocessor to use `MemoryVfs`

**Success Criteria:**
- ✅ No direct `fs::read_to_string` in compiler code
- ✅ CLI uses `CompilerSession::new_with_os_vfs()`
- ✅ All parsers work with `SourceFile` inputs

### Phase 4: Testing Infrastructure (2-3 days)
**Goal:** Fast, hermetic tests without disk I/O

**Tasks:**
1. Create VFS test utilities and helpers
2. Migrate workspace tests from `tempfile` to `MemoryVfs`
3. Write incremental compilation tests
4. Remove `tempfile` dependencies

**Success Criteria:**
- ✅ Tests run without touching filesystem
- ✅ Verify `set_text()` invalidates only affected queries
- ✅ 2-5x faster test suite

### Phase 5: LSP Integration (3-4 days)
**Goal:** Full LSP support with incremental compilation

**Tasks:**
1. Implement `LspVfs` with `Url` keys
2. Add `on_file_opened()` handler
3. Integrate with `hwml-lsp-server`
4. Wire up `textDocument/didChange` events
5. Test typing triggers selective recomputation

**Success Criteria:**
- ✅ LSP processes unsaved file changes
- ✅ Typing invalidates only affected files
- ✅ Cache hit rate >80% on incremental edits

---

## Estimated Timeline

| Phase | Duration | Dependencies |
|-------|----------|--------------|
| Phase 1 | 2-3 days | None |
| Phase 2 | 2-3 days | Phase 1 complete |
| Phase 3 | 3-4 days | Phase 2 complete |
| Phase 4 | 2-3 days | Phase 3 complete |
| Phase 5 | 3-4 days | Phase 4 complete |
| **Total** | **12-17 days** | Sequential execution |

**Note:** Phases 1-2 are critical path. Phases 3-4 can be partially parallelized per subsystem.

---

## Risk Mitigation

**Risk 1: Breaking existing CLI**
- *Mitigation:* Keep `CompilerSession::new_with_os_vfs()` behavior identical to current
- *Rollback:* Git branch protection, can revert Phase 3 independently

**Risk 2: Performance regression**
- *Mitigation:* Benchmark before/after, DashMap is already used
- *Test:* Measure file loading time on 1000+ file workspace

**Risk 3: Salsa cache not invalidating**
- *Mitigation:* Write tests in Phase 4 that verify `set_text()` works
- *Debug:* Enable Salsa event logging to verify invalidation

---

## Success Metrics

### Code Quality
- [ ] `SourceFile` defined as `#[salsa::input]` with path
- [ ] No `Arc<RwLock<Vfs>>` or `DashMap` inside `HwmlDatabase`
- [ ] No `std::fs::read_to_string` in query functions

### Functionality  
- [ ] CLI and LSP share same query paths
- [ ] Unit tests use `MemoryVfs` (no disk I/O)
- [ ] LSP incremental compilation works

### Performance
- [ ] Test suite 2-5x faster (no tempfile overhead)
- [ ] Cache hit rate >80% on incremental LSP edits
- [ ] CLI performance unchanged or better

---

## Next Steps

1. **Review this plan** with team
2. **Create git branch** `feature/vfs-implementation`
3. **Start Phase 1** (highest priority, fixes anti-pattern)
4. **Track progress** using task checklist
5. **Write tests first** for each phase (TDD approach)

---

**Status:** Ready for implementation  
**Owner:** TBD  
**Start Date:** TBD
