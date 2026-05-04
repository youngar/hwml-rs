# HWML Design Wiki

**Created:** 2026-05-02  
**Purpose:** LLM-maintained knowledge base for HWML design decisions, rationales, and research  
**Status:** Bootstrap complete, ready for use and expansion

---

## Quick Start

### For New Contributors
1. **Start here:** Read [[overview]] for high-level introduction
2. **Understand the design:** Browse [[decisions/]] for Architecture Decision Records
3. **Learn concepts:** Explore [[entities/]] for technical concepts
4. **Get oriented:** Check [[BOOTSTRAP-STATUS]] for current state

### For Existing Developers
- **Find design rationale:** Check [[decisions/]] ADRs
- **Understand a concept:** Look in [[entities/]]
- **See implementation status:** Check [[BOOTSTRAP-STATUS]]
- **Navigate everything:** Use [[index]]

---

## Structure

```
wiki/
├── README.md (this file)
├── index.md              # Complete catalog
├── log.md                # Chronological update history
├── overview.md           # HWML introduction
├── BOOTSTRAP-STATUS.md   # Current ingestion status
│
├── decisions/            # Architecture Decision Records (ADRs)
│   ├── ADR-001-lcf-kernel.md
│   ├── ADR-002-bidirectional-typing.md
│   └── ADR-004-mvs-package-manager.md
│
├── entities/             # Concepts, libraries, tools
│   └── nbe.md
│
├── components/           # System components (to be created)
├── research/             # Papers, external projects (to be created)
├── onboarding/           # Learning paths (to be created)
└── synthesis/            # Cross-cutting analyses (to be created)
```

---

## What's in the Wiki

### Architecture Decision Records (ADRs)

**Format:** Context → Alternatives → Decision → Rationale → Consequences

**Currently:**
- **ADR-001:** LCF-Style Trusted Kernel - Why only the kernel can construct terms
- **ADR-002:** Bidirectional Type Checking - How HWML's type checker works
- **ADR-004:** MVS Package Manager - Why Minimum Version Selection over SemVer

### Entities (Concepts)

**Format:** Definition → How HWML Uses It → Properties → References

**Currently:**
- **NbE:** Normalization by Evaluation - Core technique for type checking

### Overview

High-level introduction to HWML covering:
- What HWML is and its key features
- Three-layer architecture (surface → core → semantic)
- Core concepts (dependent types, bidirectional typing, NbE)
- Major components and their relationships
- Implementation status and phases

---

## How to Use

### Querying the Wiki

Ask questions about design decisions:
```
"Why did we choose the LCF kernel pattern?"
→ See ADR-001-lcf-kernel.md

"What is NbE and why do we use it?"
→ See entities/nbe.md

"How does bidirectional typing work?"
→ See ADR-002-bidirectional-typing.md

"Why MVS instead of SemVer?"
→ See ADR-004-mvs-package-manager.md
```

### Navigation

- **By topic:** Use [[index]] to find all pages by category
- **By date:** Use [[log]] to see what was created when
- **By status:** Use [[BOOTSTRAP-STATUS]] to see ingestion progress

### Adding New Content

As new design documents are created in `design/`:
1. Ask LLM to ingest the document
2. LLM extracts decisions, concepts, components
3. LLM creates/updates relevant wiki pages
4. LLM updates index and log

**Example:**
```
"Ingest design/new-feature.md"
```

---

## Relationship to Source Documents

### The Three-Layer Model

**Layer 1: Raw Sources** (`design/` directory)
- Original design documents
- **IMMUTABLE** - Wiki never modifies these
- Source of truth

**Layer 2: The Wiki** (`wiki/` directory)
- Structured, cross-referenced knowledge
- **MAINTAINED** by LLM
- Derived from sources

**Layer 3: Schema** (`WIKI.md` in root)
- Instructions for how LLM maintains the wiki
- Templates and workflows
- Co-evolved with human

### Cross-References

Every wiki page cites its sources:
- ADRs reference `design/` documents
- Entities cite papers and external projects
- All pages link to related pages

---

## Current Status

**Bootstrap Phase: COMPLETE ✅**

**Created:**
- 📊 Foundation: index, log, overview, status
- 📋 3 ADRs: LCF kernel, bidirectional typing, MVS package manager
- 🧩 1 entity: NbE
- 🔗 Cross-references established

**Progress:**
- ~10% of full ingestion complete
- Foundation solid enough for use
- Ready for continued expansion

**Next Steps:**
1. Ingest core type system documents
2. Create component pages
3. Generate onboarding guides
4. Continue batch ingestion

See [[BOOTSTRAP-STATUS]] for details.

---

## Maintenance

### LLM's Role
- Reads design documents
- Extracts decisions, concepts, relationships
- Creates structured wiki pages
- Maintains cross-references
- Updates index and log

### Human's Role
- Writes design documents (in `design/`)
- Requests ingestion
- Reviews wiki pages
- Asks questions
- Guides direction

---

## Quality Standards

Every wiki page includes:
- **Source attribution** - Which design docs it's based on
- **Confidence score** - How certain the information is
- **Status markers** - Approved, Implemented, Planned, etc.
- **Cross-references** - Links to related pages
- **Timestamps** - When created/updated

See `WIKI.md` (in root) for full schema and templates.

---

## Benefits

**For Onboarding:**
- New contributors read overview → structured learning paths
- Understand "why" through ADRs, not just "what"
- Hours to get oriented instead of weeks

**For Development:**
- Quick answers: "Why did we choose X?"
- Find related decisions and concepts
- Track implementation status

**For Project Health:**
- Preserve institutional knowledge
- Document design evolution
- Never lose decision rationale

---

## Files Reference

**Key Files:**
- `README.md` (this file) - How to use the wiki
- `index.md` - Complete page catalog
- `log.md` - Chronological history
- `overview.md` - HWML introduction
- `BOOTSTRAP-STATUS.md` - Current progress

**Schema (in root `WIKI.md`):**
- Entity type definitions
- Page templates
- Workflow descriptions
- Quality standards

---

## Questions?

- **"How do I find X?"** → Check [[index]]
- **"Why was decision Y made?"** → Look in [[decisions/]]
- **"What is concept Z?"** → Look in [[entities/]]
- **"What's been ingested?"** → Check [[BOOTSTRAP-STATUS]]
- **"How do I add new content?"** → Ask LLM to ingest design doc

---

**The wiki is ready to use and will grow with the project.**
