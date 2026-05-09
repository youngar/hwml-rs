# HWML Design Wiki - Visual Guide

**Created:** 2026-05-02
**Purpose:** Visual representation of how the wiki system works

---

## The Big Picture

```
┌─────────────────────────────────────────────────────────────────┐
│                         HWML Project                             │
│                                                                   │
│  ┌────────────────────┐              ┌─────────────────────┐   │
│  │  design/           │              │  wiki/              │   │
│  │  (RAW SOURCES)     │─────────────▶│  (LLM-GENERATED)   │   │
│  │                    │   LLM reads  │                     │   │
│  │  • ARCHITECTURE.md │   extracts   │  • ADRs             │   │
│  │  • package-mgr.md  │   organizes  │  • Entities         │   │
│  │  • 50+ docs        │              │  • Components       │   │
│  │  (IMMUTABLE)       │              │  • Research         │   │
│  └────────────────────┘              │  • Onboarding       │   │
│           ▲                           │  (MAINTAINED)       │   │
│           │                           └─────────────────────┘   │
│           │                                      │               │
│           │                                      │               │
│           │                                      ▼               │
│      Humans write                          Humans read           │
│      new design docs                       structured wiki       │
│                                                                   │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │                        WIKI.md                              │ │
│  │                   (LLM INSTRUCTIONS)                        │ │
│  │  • Entity types  • Templates  • Workflows  • Standards     │ │
│  └────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

---

## Information Flow

### 1. Ingestion
```
design/package-manager.md
         │
         │ LLM reads
         ▼
   ┌─────────────┐
   │   Extract   │
   │  Entities   │
   └─────────────┘
         │
         ├─▶ Decision: MVS for package manager
         ├─▶ Concept: Minimum Version Selection
         ├─▶ Concept: Content-addressed storage
         ├─▶ Component: Package manager
         ├─▶ Research: Go MVS paper
         └─▶ Research: Zig package manager

         ▼
   ┌─────────────┐
   │   Create    │
   │ Wiki Pages  │
   └─────────────┘
         │
         ├─▶ wiki/decisions/ADR-003-mvs-package-manager.md
         ├─▶ wiki/entities/mvs.md
         ├─▶ wiki/entities/content-addressed-storage.md
         ├─▶ wiki/components/package-manager.md
         └─▶ wiki/research/go-mvs.md

         ▼
   ┌─────────────┐
   │    Link     │
   │   & Index   │
   └─────────────┘
         │
         ├─▶ Cross-reference all pages
         ├─▶ Update wiki/index.md
         └─▶ Log to wiki/log.md
```

### 2. Query
```
Human: "Why MVS instead of SemVer?"
         │
         ▼
   ┌─────────────┐
   │   Search    │
   │  Index      │
   └─────────────┘
         │
         ▼ Found: ADR-003
   ┌─────────────┐
   │    Read     │
   │  Relevant   │
   │   Pages     │
   └─────────────┘
         │
         ├─ wiki/decisions/ADR-003-mvs-package-manager.md
         ├─ wiki/entities/mvs.md
         └─ wiki/research/go-mvs.md

         ▼
   ┌─────────────┐
   │ Synthesize  │
   │   Answer    │
   └─────────────┘
         │
         ├─ Cite sources
         ├─ Explain rationale
         └─ Link to related pages

         ▼ (optional)
   ┌─────────────┐
   │    File     │
   │  as Wiki    │
   │    Page     │
   └─────────────┘
         │
         └─▶ wiki/synthesis/mvs-vs-semver.md
```

---

## Wiki Page Relationships

```
                    wiki/overview.md
                           │
           ┌───────────────┼───────────────┐
           │               │               │
           ▼               ▼               ▼
     decisions/      components/      entities/
           │               │               │
           │               │               │
  ┌────────┼────────┐      │      ┌────────┼────────┐
  │        │        │      │      │        │        │
  ▼        ▼        ▼      ▼      ▼        ▼        ▼
ADR-001  ADR-002  ADR-003  │   kernel    nbe   bidirectional
  │        │        │      │      │        │        │
  │        │        │      │      │        │        │
  │        │        │      │      └────────┴────────┘
  │        │        │      │               │
  │        │        │      │               ▼
  │        │        │      │        research/
  │        │        │      │        papers, projects
  │        │        │      │
  │        │        │      ▼
  │        │        │  elaborator
  │        │        │      │
  └────────┴────────┴──────┴──────┐
                                  │
                                  ▼
                           onboarding/
                          new-contributor
                                  │
                                  │
                              (Uses all)
```

---

## Entity Type Hierarchy

```
Wiki Pages
    │
    ├─ Decisions (ADRs)
    │    ├─ ADR-001: LCF Kernel
    │    ├─ ADR-002: Bidirectional Typing
    │    └─ ADR-003: MVS Package Manager
    │         │
    │         ├─ Context
    │         ├─ Alternatives Considered
    │         ├─ Decision + Rationale
    │         ├─ Consequences
    │         ├─ Sources (links to design docs)
    │         └─ Related (links to other wiki pages)
    │
    ├─ Entities
    │    ├─ Concepts (NbE, Unification, etc.)
    │    ├─ Libraries (Salsa, CIRCT, etc.)
    │    └─ Phases (Phase 1, 1.5, 2+)
    │
    ├─ Components
    │    ├─ Kernel
    │    ├─ Elaborator
    │    └─ Package Manager
    │         │
    │         ├─ Purpose
    │         ├─ Architecture
    │         ├─ Dependencies (links to entities)
    │         ├─ Design Decisions (links to ADRs)
    │         └─ Implementation Status
    │
    ├─ Research
    │    ├─ Papers
    │    ├─ External Projects (GHC, Lean, etc.)
    │    └─ Comparisons
    │
    ├─ Onboarding
    │    ├─ New Contributor Guide
    │    ├─ Learning Paths
    │    └─ Topic Deep Dives
    │
    └─ Synthesis
         ├─ Design Evolution
         ├─ Trade-off Analyses
         └─ Open Questions
```

---

## Workflow Diagram

```
┌──────────────────────────────────────────────────────┐
│                    Human Actions                      │
└──────────────────────────────────────────────────────┘
                         │
         ┌───────────────┼───────────────┐
         │               │               │
         ▼               ▼               ▼
   Create Design   Ask Question    Request Lint
     Document
         │               │               │
         ▼               │               │
   design/new.md        │               │
         │               │               │
         ▼               │               │
   "Ingest new.md"      │               │
         │               │               │
┌────────┴───────────────┴───────────────┴────────────┐
│                    LLM Actions                       │
└──────────────────────────────────────────────────────┘
         │               │               │
         ▼               ▼               ▼

   INGEST          QUERY           LINT
      │               │               │
      ├─ Read doc     ├─ Search       ├─ Check orphans
      ├─ Extract      ├─ Read pages   ├─ Find contradictions
      ├─ Create pages ├─ Synthesize   ├─ Flag stale status
      ├─ Link         ├─ Cite sources ├─ Suggest fixes
      ├─ Update index └─ (File page)  └─ Report issues
      └─ Log
         │               │               │
         ▼               ▼               ▼
┌────────┴───────────────┴───────────────┴────────────┐
│                  Wiki Updated                        │
└──────────────────────────────────────────────────────┘
         │
         └─────▶ Human reads, uses, iterates
```

---

## Before and After

### Before Wiki
```
Human: "Why did we choose MVS?"

Developer:
1. Searches design/ directory
2. Finds package-manager.md
3. Reads 50-page document
4. Looks for relevant section
5. Still not sure what alternatives were considered
6. Checks git history for context
7. Maybe asks senior developer
8. Spends 30-60 minutes

Total time: 1 hour
Context gained: Partial
```

### After Wiki
```
Human: "Why did we choose MVS?"

LLM:
1. Searches wiki/index.md
2. Finds ADR-003-mvs-package-manager
3. Reads structured ADR
4. Returns answer with:
   - Context (what problem)
   - Alternatives (SemVer, manual pinning)
   - Decision (MVS)
   - Rationale (reproducibility > convenience)
   - Trade-offs
   - Sources (package-manager.md + Go MVS paper)

Total time: 30 seconds
Context gained: Complete
```

---

## Example Session Flow

```
┌─────────────────────────────────────────────┐
│ Session 1: Bootstrap                         │
└─────────────────────────────────────────────┘


Human: "Create wiki structure and ingest ARCHITECTURE.md"

LLM:
├─ Creates wiki/ directory structure
├─ Creates index.md and log.md
├─ Reads design/ARCHITECTURE.md
├─ Extracts:
│  ├─ Decision: LCF kernel
│  ├─ Decision: Bidirectional typing
│  ├─ Concept: LCF pattern
│  └─ Component: Kernel
├─ Creates 5 wiki pages
├─ Cross-links them
├─ Updates index
└─ Logs to wiki/log.md

Result: wiki/ created, 5 pages, validated structure
```

```
┌─────────────────────────────────────────────┐
│ Session 2: Query                             │
└─────────────────────────────────────────────┘

Human: "Why did we choose the LCF kernel pattern?"

LLM:
├─ Searches index.md for "LCF"
├─ Finds: ADR-001-lcf-kernel.md
├─ Reads ADR-001
├─ Synthesizes answer:
│  ├─ Context: Need type safety guarantees
│  ├─ Alternatives: unchecked, runtime checks, proof-carrying
│  ├─ Decision: LCF kernel
│  ├─ Rationale: Compile-time safety, zero cost, small TCB
│  ├─ Trade-offs: API complexity vs. safety
│  └─ Sources: ARCHITECTURE.md + LCF papers
└─ Returns structured answer with citations

Result: Complete answer in 30 seconds
```

```
┌─────────────────────────────────────────────┐
│ Session 3: Ongoing Use                       │
└─────────────────────────────────────────────┘

Developer creates: design/new-feature.md

Human: "Ingest design/new-feature.md"

LLM:
├─ Reads new-feature.md
├─ Extracts new concepts
├─ Creates/updates relevant pages
├─ Links to existing ADRs and entities
├─ Updates index
└─ Logs change

Result: Wiki automatically stays current

New contributor joins:


Contributor: "I want to work on the elaborator"

LLM:
├─ Reads wiki/onboarding/elaborator-guide.md
├─ Returns learning path:
│  ├─ Prerequisites: NbE, bidirectional typing
│  ├─ Key concepts: metavariables, unification
│  ├─ Design docs: elaboration.md, kernel-judgements.md
│  ├─ Codebase: hwml-elab/
│  └─ Implementation status: what's done, what's next
└─ Structured, actionable guidance

Result: Onboarding in hours instead of weeks
```

---

## Summary

The wiki system transforms scattered design documents into a **queryable knowledge graph** that:

✅ **Preserves context** - never lose "why" behind decisions
✅ **Accelerates onboarding** - structured paths instead of 50+ docs
✅ **Answers questions** - "why X?" gets complete rationale
✅ **Maintains itself** - LLM does the bookkeeping
✅ **Compounds value** - each doc makes wiki richer

**Time investment:** 12-16 hours to bootstrap
**Ongoing cost:** <5 minutes per new design doc
**Payoff:** Immediate for onboarding, compounds over time

---

## Next Steps

See:
- `WIKI-QUICK-START.md` - How to use the wiki
- `WIKI-SUMMARY.md` - Decision summary for approval
- `WIKI-BOOTSTRAP-PLAN.md` - Implementation steps
- `EXAMPLE-ADR.md` - What wiki pages look like