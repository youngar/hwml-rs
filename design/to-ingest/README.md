# Design Documents - To Be Ingested

**Created:** 2026-05-02  
**Purpose:** Staging area for design documents not yet processed into the wiki  
**Count:** 57 documents

---

## Status

These documents have **not yet been ingested** into the wiki. They are organized here for systematic processing.

**Processed documents remain in:** `design/` (root level)  
**Unprocessed documents are here in:** `design/to-ingest/`

---

## Priority Categories

### High Priority (Core Understanding) - ~10 documents

**Type System:**
- `elaboration.md` - Elaboration algorithm and async constraint solving
- `unification.md` - Pattern unification algorithm
- `universes.md` - Universe hierarchy and levels
- `kernel-judgements.md` - Typing rules details
- `pattern-matching.md` - Pattern compilation

**Two-Level Type Theory:**
- `2ltt-nbe.md` - NbE for staged computation
- `2ltt-csp.md`, `2ltt-quote.md`, `2ltt-stuck-splice.md` - 2LTT details

**Implementation:**
- `NbE-IMPLEMENTATION-PLAN.md` - NbE implementation details
- `PHASE1-COMPLETE.md` - Phase 1 completion status
- `PHASE1.5-PLAN.md` - Current phase goals

### Medium Priority (Implementation Details) - ~15 documents

**LET Expression (9 documents):**
- `LET_IMPLEMENTATION_FINAL.md`
- `LET_CORRECTED_DESIGN.md`
- `LET_DATA_FLOW.md`
- `LET_DELTA_REDUCTION_REFACTOR.md`
- `LET_IMPLEMENTATION_CHECKLIST.md`
- `LET_IMPLEMENTATION_PLAN.md`
- `LET_IMPLEMENTATION_SUMMARY.md`
- `LET_KEY_INSIGHT.md`
- `LET_TECHNICAL_DESIGN.md`

**Location/Debug (6 documents):**
- `location-information-design.md`
- `location-design-comparison.md`
- `location-example-workflow.md`
- `location-ranges-update.md`
- `debug-info-research.md`
- `salsa-location-architecture.md`

**Tooling:**
- `lsp-object-file-research.md`
- `mdbook-integreation.md`

**Comparisons:**
- `nbe-vs-legacy-comparison.md`
- `COMPARISON-SUMMARY.md`

**Other:**
- `async-unification-tutorial.md`
- `metavariable-migration-guide.md`
- `LEGACY-TO-TYPECODE-MIGRATION.md`

### Lower Priority (Specialized) - ~30+ documents

**NbE Related:**
- `Staged-nbe.md`
- `README-NbE.md`
- `nbe-architecture.md`
- `nbe-migration-map.md`
- `nbe-phase1-implementation.md`
- `nbe-quick-reference.md`

**Universe Related:**
- `universes_and_shunting.md`
- `universes_and_shunting2.md`

**Implementation Plans:**
- `implementation-plan-lcf.md`
- `type-checking-implementation-plan.md`

**Workflow & Process:**
- `eda-workflow-comprehensive.md`
- `better-elaboration.md`
- `hwml-evaluation-strategy.md`
- `hwml-reorg.md`

**Specific Features:**
- `case-splitting.md`
- `poisoned-metavariables.md`
- `renaming.md`
- `simulation-model-stubbing.md`

**Verification:**
- `SOLVER-VERIFICATION.md`
- `EXEL-PATTERN-VERIFICATION.md`

**Errors & Mistakes:**
- `HETEROGENEOUS-EQUALITY-MISTAKE.md`

**Misc:**
- `Notes.md`
- `docs.md`

---

## How to Ingest

### Individual Documents
```
"Ingest design/to-ingest/elaboration.md"
"Ingest design/to-ingest/unification.md"
```

### By Category
```
"Ingest all type system documents from to-ingest/"
"Process all LET-related documents"
"Ingest all NbE documents"
```

### Batch Processing
```
"Ingest all high-priority documents from to-ingest/"
"Process everything in to-ingest/"
```

---

## Expected Outputs

### From Type System Docs
**Will create:**
- ADR-003: Async Elaboration
- Entity: Pattern Unification
- Entity: Universe Hierarchy
- Component: Elaborator (detailed)
- Research: Unification algorithms

### From LET Docs
**Will create:**
- ADR: LET expression design
- Synthesis: LET implementation evolution
- Research: Delta reduction

### From Location Docs
**Will create:**
- ADR: Source location architecture
- Component: Location tracking
- Research: Salsa integration

### From NbE Docs
**Will expand:**
- Entity: NbE (much more detail)
- Research: Staged NbE
- Component: Kernel (NbE implementation)

---

## Notes

- All documents here are **source material** - not wiki pages
- After ingestion, documents stay here (for reference)
- Wiki pages go in `wiki/` directory
- Original design docs in `design/` root are the primary sources

---

## Progress Tracking

**Total documents in to-ingest:** 57  
**High priority remaining:** ~10  
**Medium priority remaining:** ~15  
**Lower priority remaining:** ~32

**Estimated ingestion time:**
- High priority: 6-8 hours
- Medium priority: 8-10 hours
- Lower priority: 12-15 hours
- **Total:** 25-35 hours for complete ingestion

**Can be done incrementally** - as needed for development.

---

## See Also

- `../README.md` - Design docs index (for processed docs)
- `../../wiki/index.md` - Wiki index
- `../../wiki/BOOTSTRAP-STATUS.md` - Current ingestion progress
