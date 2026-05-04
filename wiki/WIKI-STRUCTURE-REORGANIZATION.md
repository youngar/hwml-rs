# Wiki Structure Reorganization (VFS Documentation)

**Date:** 2026-05-04  
**Change:** Separated ADRs from implementation guides

---

## Problem

The VFS review generated multiple documents that were all placed in `wiki/decisions/`:
- ADR-008 (the architectural decision) ✅ Correct location
- Implementation plan ❌ Wrong location
- Phase-by-phase code examples ❌ Wrong location
- Quickstart guide ❌ Wrong location
- Review summary ❌ Wrong location

**Issue:** ADRs should contain architectural decisions, not implementation details.

---

## New Structure

Following the existing pattern used by `FRONTEND-IMPLEMENTATION-PLAN.md` and `FRONTEND-ARCHITECTURE-SUMMARY.md`:

```
wiki/
├── VFS-IMPLEMENTATION-PLAN.md          # High-level plan (root level)
├── VFS-REVIEW-SUMMARY.md               # Review summary (root level)
│
├── decisions/                          # ADRs only
│   └── ADR-008-vfs-abstraction.md     # The architectural decision
│
└── implementation/                     # NEW: Detailed implementation guides
    ├── README.md                       # Explains this directory
    └── vfs/
        ├── quickstart.md               # Quick reference
        ├── phase1-fix-anti-pattern.md  # Detailed Phase 1 code
        ├── phase2-vfs-foundation.md    # Detailed Phase 2 code
        ├── phase3-migration.md         # Detailed Phase 3 code
        └── phase4-5-testing-lsp.md     # Detailed Phase 4-5 code
```

---

## Rationale

### Root Level (`wiki/`)
**Purpose:** High-level summaries and plans that synthesize multiple ADRs  
**Naming:** `UPPERCASE-WITH-DASHES.md`  
**Examples:**
- `FRONTEND-IMPLEMENTATION-PLAN.md`
- `FRONTEND-ARCHITECTURE-SUMMARY.md`
- `VFS-IMPLEMENTATION-PLAN.md` ✅
- `VFS-REVIEW-SUMMARY.md` ✅

### `wiki/decisions/`
**Purpose:** Architectural Decision Records (ADRs)  
**Naming:** `ADR-NNN-short-description.md`  
**Content:** The "what" and "why" of architectural choices  
**Stability:** Relatively stable, only updated when decisions change

### `wiki/implementation/` (NEW)
**Purpose:** Detailed implementation guides with code examples  
**Naming:** `phase-N-description.md` or `quickstart.md`  
**Content:** The "how" - step-by-step code examples, migration guides  
**Stability:** Working documents, may evolve during implementation

---

## Files Moved

### From `wiki/decisions/` → `wiki/`
- `ADR-008-implementation-plan.md` → `VFS-IMPLEMENTATION-PLAN.md`
- `ADR-008-REVIEW-SUMMARY.md` → `VFS-REVIEW-SUMMARY.md`

### From `wiki/decisions/` → `wiki/implementation/vfs/`
- `ADR-008-phase1-code-examples.md` → `phase1-fix-anti-pattern.md`
- `ADR-008-phase2-code-examples.md` → `phase2-vfs-foundation.md`
- `ADR-008-phase3-code-examples.md` → `phase3-migration.md`
- `ADR-008-phase4-5-examples.md` → `phase4-5-testing-lsp.md`
- `ADR-008-QUICKSTART.md` → `quickstart.md`

### Unchanged
- `decisions/ADR-008-vfs-abstraction.md` ✅ (stays in decisions)

---

## Link Updates

All internal wiki links have been updated:
- `[[ADR-008-implementation-plan]]` → `[[VFS-IMPLEMENTATION-PLAN]]`
- `[[ADR-008-phase1-code-examples]]` → `[[implementation/vfs/phase1-fix-anti-pattern]]`
- etc.

Cross-references now properly distinguish between:
- The **ADR** (architectural decision): `[[decisions/ADR-008-vfs-abstraction]]`
- The **plan** (high-level strategy): `[[VFS-IMPLEMENTATION-PLAN]]`
- The **guides** (detailed code): `[[implementation/vfs/phase1-fix-anti-pattern]]`

---

## Benefits

1. **Clearer separation of concerns**
   - ADRs = architectural decisions (stable)
   - Implementation guides = how to build it (working documents)

2. **Consistent with existing patterns**
   - Follows same structure as frontend docs
   - Uses established naming conventions

3. **Better discoverability**
   - High-level plans at wiki root
   - Detailed guides in dedicated directory
   - Clear hierarchy

4. **Easier maintenance**
   - Implementation details can evolve independently from ADRs
   - ADRs stay focused on decisions, not implementation

---

## Future Pattern

For new features, follow this structure:

```
wiki/
├── MY-FEATURE-IMPLEMENTATION-PLAN.md    # High-level plan (root)
├── MY-FEATURE-SUMMARY.md                # Summary/review (root)
│
├── decisions/
│   └── ADR-NNN-my-feature.md            # The decision (decisions/)
│
└── implementation/
    └── my-feature/                      # Implementation guides
        ├── quickstart.md
        ├── phase1-*.md
        └── phase2-*.md
```

---

## Verification

All VFS documentation is now properly organized:

```bash
# Check structure
find wiki -type f -name "*.md" | grep -E "(VFS|vfs|ADR-008)"

# Should show:
# wiki/VFS-IMPLEMENTATION-PLAN.md
# wiki/VFS-REVIEW-SUMMARY.md
# wiki/decisions/ADR-008-vfs-abstraction.md
# wiki/implementation/vfs/phase1-fix-anti-pattern.md
# wiki/implementation/vfs/phase2-vfs-foundation.md
# wiki/implementation/vfs/phase3-migration.md
# wiki/implementation/vfs/phase4-5-testing-lsp.md
# wiki/implementation/vfs/quickstart.md
```

✅ Structure verified and all links updated.
