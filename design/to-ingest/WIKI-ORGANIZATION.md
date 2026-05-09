# HWML Design Wiki - Organization Summary

**Date:** 2026-05-02  
**Status:** Files reorganized for systematic ingestion

---

## Directory Structure

```
hwml-rust/
├── WIKI.md                           # LLM instructions for wiki maintenance
├── WIKI-ORGANIZATION.md             # This file
│
├── design/                          # Design documents
│   ├── README.md                    # Index of processed docs
│   │
│   ├── ARCHITECTURE.md              # ✅ Processed → ADR-001, ADR-002
│   ├── package-manager.md           # ✅ Processed → ADR-004
│   ├── hwml.md                      # ✅ Partially → overview
│   │
│   ├── WIKI-*.md (7 files)          # Wiki system documentation
│   ├── LLMWiki.md                   # Original pattern documentation
│   ├── EXAMPLE-ADR.md               # Example wiki output
│   │
│   └── to-ingest/                   # 📦 57 unprocessed documents
│       ├── README.md                # Organization by priority
│       ├── elaboration.md           # High priority
│       ├── unification.md           # High priority
│       ├── LET_*.md (9 files)       # Medium priority
│       ├── location-*.md (4 files)  # Medium priority
│       └── ... (remaining files)
│
└── wiki/                            # 📚 LLM-generated knowledge base
    ├── README.md                    # How to use the wiki
    ├── index.md                     # Complete catalog
    ├── log.md                       # Chronological history
    ├── overview.md                  # HWML introduction
    ├── BOOTSTRAP-STATUS.md          # Progress tracker
    │
    ├── decisions/                   # Architecture Decision Records
    │   ├── ADR-001-lcf-kernel.md
    │   ├── ADR-002-bidirectional-typing.md
    │   └── ADR-004-mvs-package-manager.md
    │
    ├── entities/                    # Concepts, libraries, tools
    │   └── nbe.md
    │
    ├── components/                  # System components (to create)
    ├── research/                    # Papers, external projects (to create)
    ├── onboarding/                  # Learning paths (to create)
    └── synthesis/                   # Cross-cutting analyses (to create)
```

---

## File Categories

### Processed Documents (in `design/`)
**Count:** 3 design docs + 7 wiki system docs

**Design docs fully ingested:**
1. `ARCHITECTURE.md` → ADR-001, ADR-002, kernel concepts
2. `package-manager.md` → ADR-004, package management design
3. `hwml.md` → Overview content (partial)

**Wiki system docs (kept for reference):**
- `WIKI-SYSTEM-PROPOSAL.md` - Full wiki design
- `WIKI-BOOTSTRAP-PLAN.md` - Implementation plan
- `WIKI-QUICK-START.md` - User guide
- `WIKI-SUMMARY.md` - Decision summary
- `WIKI-VISUAL-GUIDE.md` - Diagrams and workflows
- `WIKI-INDEX.md` - Navigation guide
- `LLMWiki.md` - Original pattern
- `EXAMPLE-ADR.md` - Example outputs

### Unprocessed Documents (in `design/to-ingest/`)
**Count:** 57 documents

**Priority breakdown:**
- High priority (core understanding): ~10 documents
- Medium priority (implementation): ~15 documents
- Lower priority (specialized): ~32 documents

**See:** `design/to-ingest/README.md` for complete categorization

### Wiki Pages (in `wiki/`)
**Count:** 9 pages created

**Foundation:**
- README.md, index.md, log.md, overview.md, BOOTSTRAP-STATUS.md

**Content:**
- 3 ADRs (decisions/)
- 1 entity (entities/)
- Components, research, onboarding, synthesis (directories ready)

---

## Workflow

### Adding New Design Documents
1. Create document in `design/` (or `design/to-ingest/`)
2. Request ingestion: "Ingest design/new-doc.md"
3. LLM processes and creates wiki pages
4. Document stays in `design/` for reference

### Querying the Wiki
```
"What is HWML?" → wiki/overview.md
"Why LCF kernel?" → wiki/decisions/ADR-001-lcf-kernel.md
"Why MVS?" → wiki/decisions/ADR-004-mvs-package-manager.md
```

### Continuing Ingestion
```
"Ingest design/to-ingest/elaboration.md"
"Process all high-priority documents"
"Create component pages from existing knowledge"
```

---

## Benefits of This Organization

### Clear Separation
✅ **Processed** (design/ root) vs **Unprocessed** (design/to-ingest/)  
✅ **Source** (design/) vs **Derived** (wiki/)  
✅ **Documentation** (WIKI-*.md) vs **Content** (everything else)

### Systematic Processing
✅ 57 documents organized by priority  
✅ Can ingest incrementally or in batches  
✅ Easy to track progress

### Maintainability
✅ All original docs preserved  
✅ Wiki can be regenerated  
✅ Version controlled (git)

---

## Current Status

**Bootstrap:** ✅ COMPLETE

**Progress:**
- Documents processed: 3 / ~60 (5%)
- Wiki pages created: 9 foundation pages
- ADRs: 3 / ~12-15 needed
- Entities: 1 / ~20-25 needed
- Components: 0 / ~6 needed

**Next Steps:**
1. Ingest high-priority type system docs (10 files)
2. Create component pages (3-6 pages)
3. Generate onboarding guides (3-5 pages)
4. Continue batch ingestion as needed

---

## Key Files to Know

**Getting Started:**
- `wiki/README.md` - Start here to understand the wiki
- `wiki/overview.md` - Introduction to HWML
- `design/README.md` - What's in design/

**Reference:**
- `wiki/index.md` - Find any wiki page
- `design/to-ingest/README.md` - What needs ingestion
- `WIKI.md` (root) - LLM instructions/schema

**Progress Tracking:**
- `wiki/BOOTSTRAP-STATUS.md` - Current state
- `wiki/log.md` - What's been done

**Planning:**
- `design/WIKI-SYSTEM-PROPOSAL.md` - Full system design
- `design/WIKI-BOOTSTRAP-PLAN.md` - Implementation plan

---

## Usage Examples

### For New Contributors
```
1. Read wiki/README.md
2. Read wiki/overview.md  
3. Browse wiki/decisions/ for key decisions
4. Ask questions about specific topics
```

### For Developers
```
"I'm working on elaboration - what do I need to know?"
→ LLM ingests relevant docs and synthesizes answer

"Create a component page for the kernel"
→ LLM uses ADR-001, ADR-002, ARCHITECTURE.md

"What's the status of Phase 1.5?"
→ LLM can ingest PHASE1.5-PLAN.md on demand
```

### For Systematic Processing
```
"Ingest all type system documents (high priority)"
"Create all component pages"
"Generate onboarding guides"
"Process remaining medium-priority documents"
```

---

## Notes

- **Non-destructive:** Original design docs never modified
- **Incremental:** Can process docs as needed
- **Flexible:** Wiki pages can be regenerated/improved
- **Scalable:** Structure supports growth to 100+ docs

**The system is operational and ready for continued use.**
