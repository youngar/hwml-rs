# Location Information - Implementation Documentation

This directory contains implementation plans and cleanup tasks for HWML's location tracking system.

---

## Current Status (2026-05-06)

**Decision:** Byte-level spans only, no line:column in AST
**Status:** Cleanup needed - remove experimental code
**Priority:** Medium - cleanup to align with final architecture

---

## Active Documents (Cleanup)

### 🧹 Cleanup Task Lists (USE THESE)

1. **`CLEANUP-CHECKLIST.md`** ⭐ - **Quick execution checklist**
   - Pre-flight checks
   - Phase-by-phase checklist
   - Verification steps
   - ~2-3 hours of work

2. **`cleanup-task-list.md`** - **Detailed task breakdown**
   - Phase 1: hwml-surface cleanup
   - Phase 2: hwml-core cleanup
   - Phase 3: Verification
   - Complete with time estimates

3. **`cleanup-code-changes.md`** - **Exact code to delete/modify**
   - Line-by-line change instructions
   - Before/after code snippets
   - 5 files modified, ~349 lines deleted

4. **`cleanup-findings.md`** - **What was found in codebase**
   - Complete search results
   - Impact analysis
   - Dependency review

---

## Historical Documents (Reference Only)

These describe a **different approach** that was considered but **not adopted**:

- `deep-dive-task-list.md` - Line:column tracking implementation plan (historical)
- `parser-migration-guide.md` - Migration to line:column (historical)
- `streaming-lexer-advantage.md` - Streaming line:column tracking (historical)

---

## Final Architecture (ADR-014)

**Byte-level spans only:**
- Surface AST stores `Range<usize>` (byte offsets)
- Core IR has NO location fields
- Lazy `LineInfo` conversion for diagnostics
- No line:column tracking during parsing

See: `wiki/decisions/ADR-014-byte-level-location-tracking.md`

---

## Cleanup Goal

Remove experimental line:column tracking code:
- ❌ `LineColRange` type
- ❌ `LocLexer` class
- ❌ `ParserContext` class
- ❌ `Position` type (hwml-core)
- ❌ `Location` type (hwml-core)

Keep byte-range infrastructure:
- ✅ `LineInfo` (hwml-support) for lazy conversion
- ✅ `SourceRange` (hwml-core) for error reporting
- ✅ Byte ranges in surface AST

---

## Quick Start

1. Read `CLEANUP-CHECKLIST.md` for quick execution guide
2. Review `cleanup-findings.md` to see what was found
3. Use `cleanup-code-changes.md` for exact code snippets
4. Execute cleanup following the checklist
5. Run tests to verify

**Estimated time:** 2-3 hours

---

## Related Documentation

- **Current ADR:** `wiki/decisions/ADR-014-byte-level-location-tracking.md`
- **UTF-8 Handling:** `wiki/decisions/ADR-013-utf8-internal-representation.md`
- **Implementation Review:** `wiki/analysis/lexer-parser-location-tracking-review.md`
- **Historical Design:** `design/to-ingest/location-information-design.md` (not adopted)
