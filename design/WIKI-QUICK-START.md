# HWML Design Wiki - Quick Start

**Created:** 2026-05-02  
**For:** New users of the HWML Design Wiki system

---

## What Is This?

The HWML Design Wiki is an **LLM-maintained knowledge base** that organizes all design decisions, rationales, and research for the HWML project. Instead of manually maintaining documentation, an LLM agent:
- Reads design documents
- Extracts key information
- Builds a structured wiki with cross-references
- Answers questions about design decisions
- Keeps everything up-to-date automatically

Think of it as a librarian that never gets tired of filing, cross-referencing, and summarizing.

---

## File Guide

### 📄 Start Here (in order)

1. **LLMWiki.md** - The pattern/philosophy (read first)
   - Explains the core idea
   - Written by Andrej Karpathy + agentmemory team
   - Generic pattern, not HWML-specific

2. **WIKI-SYSTEM-PROPOSAL.md** - HWML-specific design
   - How we adapt LLM Wiki for HWML
   - Directory structure
   - Entity types (ADRs, components, concepts)
   - Implementation phases

3. **WIKI.md** (root directory) - Schema/instructions for the LLM
   - Templates for wiki pages
   - Workflows (ingest, query, lint)
   - Confidence scoring
   - HWML-specific conventions

4. **WIKI-BOOTSTRAP-PLAN.md** - Step-by-step execution plan
   - How to actually build the wiki
   - Which docs to ingest first
   - Validation steps
   - Success metrics

5. **This file** - Quick reference for humans

---

## Quick Commands

### As a Human User

**To add a new design document to the wiki:**
```
You: "Ingest design/new-feature.md"
```

**To ask about design decisions:**
```
You: "Why did we choose bidirectional typing?"
You: "What are the trade-offs of MVS vs SemVer?"
You: "How does the LCF kernel work?"
```

**To find related information:**
```
You: "What design docs relate to elaboration?"
You: "Show me everything about NbE"
```

**To check wiki health:**
```
You: "Run a lint pass"
You: "Are there any contradictions in the wiki?"
You: "What concepts are mentioned but don't have pages yet?"
```

**For onboarding:**
```
You: "I'm new to HWML and want to understand the type system"
You: "How do I start contributing to the elaborator?"
```

---

## Directory Structure

```
hwml-rust/
├── WIKI.md                    # Schema (instructions for LLM)
├── design/                    # Raw sources (IMMUTABLE)
│   ├── LLMWiki.md            # Pattern documentation
│   ├── WIKI-SYSTEM-PROPOSAL.md
│   ├── WIKI-BOOTSTRAP-PLAN.md
│   ├── WIKI-QUICK-START.md   # This file
│   ├── ARCHITECTURE.md        # Design docs (never modified by LLM)
│   ├── package-manager.md
│   └── ... (50+ files)
└── wiki/                      # LLM-generated (MAINTAINED BY LLM)
    ├── index.md               # Catalog of all pages
    ├── log.md                 # Chronological history
    ├── overview.md            # High-level HWML overview
    ├── entities/              # Concepts, libraries, etc.
    │   ├── nbe.md
    │   ├── salsa.md
    │   └── ...
    ├── decisions/             # Architecture Decision Records
    │   ├── ADR-001-lcf-kernel.md
    │   ├── ADR-002-mvs-package-manager.md
    │   └── ...
    ├── components/            # System components
    │   ├── kernel.md
    │   ├── elaborator.md
    │   └── ...
    ├── research/              # Papers, external projects
    │   ├── type-theory-foundations.md
    │   ├── ghc-patterns.md
    │   └── ...
    ├── onboarding/            # Learning paths
    │   ├── new-contributor-guide.md
    │   └── ...
    └── synthesis/             # Cross-cutting analyses
        ├── design-evolution.md
        └── ...
```

---

## How It Works

### 1. Ingestion
```
You: "Ingest design/package-manager.md"

LLM:
├─ Reads design/package-manager.md
├─ Extracts: MVS decision, content-addressed storage, etc.
├─ Creates: wiki/decisions/ADR-003-mvs-package-manager.md
├─ Creates: wiki/entities/mvs.md
├─ Creates: wiki/components/package-manager.md
├─ Updates: wiki/index.md
└─ Logs: wiki/log.md
```

### 2. Query
```
You: "Why MVS instead of SemVer?"

LLM:
├─ Searches: wiki/index.md
├─ Reads: wiki/decisions/ADR-003-mvs-package-manager.md
├─ Synthesizes answer with citations
└─ (Optional) Files answer as synthesis page if valuable
```

### 3. Lint
```
You: "Lint the wiki"

LLM:
├─ Checks for orphaned pages
├─ Finds contradictions
├─ Flags stale status markers
├─ Suggests missing cross-references
└─ Reports findings
```

---

## Key Concepts

### ADR (Architecture Decision Record)
Structured page capturing:
- What problem we were solving
- What alternatives we considered
- What we chose and why
- Trade-offs and consequences
- Sources and references

**Example:** ADR-002: MVS for Package Management

### Entity Page
Page for a concept, library, or tool:
- Clear definition
- How HWML uses it
- Related concepts
- References

**Example:** entities/nbe.md (Normalization by Evaluation)

### Component Page
Page for a major system component:
- Purpose and architecture
- Dependencies
- Implementation status
- Related decisions

**Example:** components/elaborator.md

---

## Benefits

### For New Contributors
- Read `wiki/onboarding/new-contributor-guide.md` instead of 50+ design docs
- Follow structured learning paths
- Understand "why" not just "what"

### For Current Developers
- Quick answers to "why did we do X?"
- Find all related docs for a topic
- Track what's designed vs. implemented
- Reference ADRs in code/PRs

### For Project Health
- Never lose design rationale
- Preserve institutional knowledge
- See evolution of ideas over time
- Onboard faster as team grows

---

## Current Status

As of 2026-05-02:
- [x] Pattern documented (LLMWiki.md)
- [x] HWML-specific design (WIKI-SYSTEM-PROPOSAL.md)
- [x] Schema created (WIKI.md)
- [x] Bootstrap plan (WIKI-BOOTSTRAP-PLAN.md)
- [ ] Wiki directory created
- [ ] First docs ingested
- [ ] Validation complete
- [ ] Full integration

**Next step:** Review proposal, then execute bootstrap plan.

---

## FAQ

**Q: Will this modify my design docs?**  
A: No! The LLM only READS from `design/`. All LLM output goes to `wiki/`.

**Q: What if the LLM makes mistakes?**  
A: The wiki is version controlled. You can review, correct, and regenerate. The LLM cites sources, making errors easy to catch.

**Q: How much work is this to maintain?**  
A: Almost none. The LLM does the bookkeeping. You just add new design docs as normal.

**Q: Do I need special tools?**  
A: No. The wiki is markdown files. View with any editor. Obsidian is nice for graph view but optional.

**Q: Can multiple people use this?**  
A: Yes! The wiki is in git. Standard collaboration workflow.

**Q: What if I don't like a generated page?**  
A: Tell the LLM to regenerate it, or edit it manually. It's your wiki.

---

## Next Steps

### To Get Started

1. **Review the proposal:**
   - Read WIKI-SYSTEM-PROPOSAL.md
   - Decide if this approach fits HWML

2. **Execute bootstrap:**
   - Follow WIKI-BOOTSTRAP-PLAN.md
   - Start with 5 key docs
   - Validate structure

3. **Iterate:**
   - Adjust based on what works
   - Expand gradually
   - Integrate into workflow

### Questions?

Ask the LLM:
```
"I have questions about the wiki system design"
"Show me an example of what an ADR would look like"
"What would the entity page for NbE contain?"
```

---

## Learn More

- **Pattern origin:** [Andrej Karpathy's LLM Wiki](https://gist.github.com/karpathy/442a6bf555914893e9891c11519de94f)
- **Extended pattern:** [agentmemory](https://github.com/rohitg00/agentmemory)
- **See:** `design/LLMWiki.md` for full background
