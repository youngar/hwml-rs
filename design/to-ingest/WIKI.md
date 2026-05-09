# HWML Design Wiki Schema

This document defines how the LLM Agent maintains the HWML Design Wiki.

---

## Purpose

The HWML Design Wiki is a **persistent, LLM-maintained knowledge base** that:
- Preserves design decisions and their rationales
- Tracks research and references that informed the design
- Provides structured onboarding for new contributors
- Maintains cross-references between concepts, decisions, and implementations
- Serves as a living memory of why HWML is designed the way it is

**You (the LLM) are the wiki maintainer.** The human curates sources, asks questions, and provides direction. You handle all bookkeeping, cross-referencing, and maintenance.

---

## Architecture

### Three Layers

1. **Raw Sources** (`design/` directory)
   - Existing design documents (IMMUTABLE)
   - Papers, external references
   - You READ from these but NEVER modify them

2. **The Wiki** (`wiki/` directory)
   - LLM-generated, structured knowledge base
   - You WRITE and MAINTAIN all files here
   - Organized by category (entities, decisions, components, research, onboarding, synthesis)

3. **This Schema** (`WIKI.md`)
   - Instructions for wiki structure and maintenance
   - Co-evolved with human over time

---

## Entity Types

Every concept, decision, or component gets a page. Use these types:

### 1. Concept
**Path:** `wiki/entities/{name}.md`  
**Purpose:** Technical concepts that HWML uses or implements

**Template:**
```markdown
# {Concept Name}

**Type:** Concept  
**Status:** {Foundational|In-Use|Experimental|Deprecated}  
**Confidence:** {0.0-1.0}

## Definition

{Clear, concise definition}

## How HWML Uses It

{Specific usage in HWML context}

## Key Properties

- Property 1
- Property 2

## Related Concepts

- [[concept-a]] - relationship description
- [[concept-b]] - relationship description

## References

- Papers, blog posts, external docs
- Links to design/ source documents

## Implementation Status

{Where in codebase, what phase}
```

**Examples:** NbE, Bidirectional Typing, Pattern Unification, Universe Hierarchies

### 2. Decision (ADR)
**Path:** `wiki/decisions/ADR-{NNN}-{slug}.md`  
**Purpose:** Architecture Decision Records

**Template:**
```markdown
# ADR-{NNN}: {Decision Title}

**Status:** {Proposed|Approved|Implemented|Superseded|Deprecated}  
**Date:** {YYYY-MM-DD}  
**Confidence:** {0.0-1.0}

## Context

{What problem were we solving? What constraints?}

## Alternatives Considered

### Option 1: {Name}
- **Pros:** ...
- **Cons:** ...
- **Sources:** ...

### Option 2: {Name}
- **Pros:** ...
- **Cons:** ...
- **Sources:** ...

## Decision

{What we chose and why}

## Rationale

{Detailed reasoning}

## Consequences

**Positive:**
- ...

**Negative:**
- ...

**Trade-offs:**
- ...

## Sources

- Links to design docs
- Papers, discussions
- External projects

## Related

- Links to other ADRs, entities, components

## Implementation

- **Phase:** {Phase N}
- **Crate:** {crate name}
- **Status:** {Not Started|In Progress|Complete}
```

### 3. Component
**Path:** `wiki/components/{name}.md`
**Purpose:** Major system components (kernel, elaborator, package manager, etc.)

**Template:**
```markdown
# {Component Name}

**Type:** Component
**Crate:** {crate-name}
**Status:** {Designed|In Progress|Complete|Deprecated}
**Phase:** {Phase N}

## Purpose

{What this component does}

## Architecture

{High-level design}

## Key Concepts Used

- [[concept-a]]
- [[concept-b]]

## Dependencies

- [[component-x]] - why needed
- [[library-y]] - purpose

## Design Decisions

- [[ADR-NNN]] - decision affecting this component

## Implementation Status

- [ ] Task 1
- [x] Task 2
- [ ] Task 3

## Source Documents

- `design/file.md`

## Related

- Links to other components
```

**Examples:** Kernel, Elaborator, Package Manager, LSP Server, CIRCT Backend

### 4. Research
**Path:** `wiki/research/{topic}.md`
**Purpose:** Research threads, paper summaries, external project analysis

**Template:**
```markdown
# {Research Topic}

**Type:** Research
**Last Updated:** {YYYY-MM-DD}

## Overview

{What this research covers}

## Key Papers

### Paper 1
- **Title:** ...
- **Authors:** ...
- **Year:** ...
- **Key Insights:** ...
- **How HWML Uses It:** ...

## External Projects

### Project 1
- **Name:** ...
- **URL:** ...
- **What We Learned:** ...
- **Applied In:** [[decision]] or [[component]]

## Open Questions

- Question 1?
- Question 2?

## Related

- Links to decisions/components informed by this research
```

**Examples:** Type Theory Foundations, GHC Patterns, Lean 4 Elaboration

### 5. Onboarding
**Path:** `wiki/onboarding/{topic}.md`
**Purpose:** Structured learning paths for new contributors

**Template:**
```markdown
# {Onboarding Topic}

**Type:** Onboarding
**Audience:** {New Contributors|Core Developers|Type Theory Background|etc.}
**Estimated Time:** {hours/days}

## Prerequisites

- Concept/skill 1
- Concept/skill 2

## Learning Path

1. **Start Here:** [[overview]]
2. **Core Concepts:**
   - [[concept-a]] - {why important}
   - [[concept-b]] - {why important}
3. **Key Decisions:**
   - [[ADR-NNN]] - {why relevant}
4. **Dive Deep:**
   - Read `design/file.md`
   - Explore `crates/name/`

## Hands-On Exercises

1. Exercise 1
2. Exercise 2

## Common Questions

**Q: Why does HWML use X instead of Y?**
A: See [[ADR-NNN]]

## Next Steps

After completing this path, you're ready to:
- Contribute to [[component]]
- Explore [[research-topic]]
```

**Examples:** New Contributor Guide, Type System Deep Dive, Elaborator Development

---

## Special Files

### index.md
**Path:** `wiki/index.md`
**Purpose:** Catalog of all wiki pages

**Structure:**
```markdown
# HWML Design Wiki Index

**Last Updated:** {YYYY-MM-DD}
**Total Pages:** {N}

## Decisions (ADRs)

- [[ADR-001]] - {one-line summary}
- [[ADR-002]] - {one-line summary}

## Components

- [[kernel]] - {one-line summary}
- [[elaborator]] - {one-line summary}

## Concepts

- [[nbe]] - {one-line summary}
- [[bidirectional-typing]] - {one-line summary}

## Research

- [[type-theory-foundations]] - {one-line summary}

## Onboarding

- [[new-contributor-guide]] - {one-line summary}

## Synthesis

- [[design-evolution]] - {one-line summary}
```

**Maintenance:** Update on every ingest, keep sorted alphabetically within sections.

### log.md
**Path:** `wiki/log.md`
**Purpose:** Chronological record of wiki updates

**Entry format:**
```markdown
## [YYYY-MM-DD] {operation} | {title}

**Sources:** {source files}
**Pages Updated:** {count}
**New Pages:** [[page1]], [[page2]]
**Notes:** {brief summary}
```

**Examples:**
```markdown
## [2026-05-02] bootstrap | Initial wiki creation
## [2026-05-03] ingest | package-manager.md
## [2026-05-04] query | "What are the MVS trade-offs?"
## [2026-05-05] lint | Found 3 orphaned concepts
```

---

## Workflows

### 1. Ingest Source Document

**Command:** `ingest design/filename.md`

**Steps:**
1. **Read** the source document
2. **Extract** entities, decisions, concepts
3. **For each entity:**
   - Check if page exists
   - Create new page OR update existing page
   - Add confidence score based on sources
   - Add timestamp
4. **Cross-reference:**
   - Add links to related pages
   - Update related pages to link back
5. **Update** `index.md` (add new entries)
6. **Log** to `log.md`

**Quality checks:**
- Every claim cites source
- Confidence scores assigned
- Status markers present
- Cross-references bidirectional

### 2. Answer Query

**Command:** User asks a question

**Steps:**
1. **Search** `index.md` for relevant pages
2. **Read** relevant wiki pages
3. **Synthesize** answer with citations
4. **Self-evaluate** answer quality (0.0-1.0)
5. **If quality > 0.8:**
   - File answer as synthesis page
   - Update related pages
   - Update index
   - Log

**Answer format:**
- Clear, structured response
- Cite wiki pages: [[page-name]]
- Cite source docs: `design/file.md`
- Mark confidence on uncertain claims

### 3. Lint

**Command:** `lint` or scheduled automatically

**Checks:**
1. **Orphans:** Pages with no inbound links
2. **Contradictions:** Conflicting claims between pages
3. **Stale status:** "Planned" features now implemented
4. **Broken links:** References to non-existent pages
5. **Missing concepts:** Mentioned but no dedicated page
6. **Low confidence:** Claims with confidence < 0.5

**Actions:**
- Auto-fix what you can (broken links, simple updates)
- Flag issues for human review
- Suggest new pages to create
- Propose consolidations

---

## Relationship Types

Use these when cross-referencing:

- **uses:** Component uses concept/library
- **depends-on:** Component depends on component
- **implements:** Code implements design
- **supersedes:** New decision replaces old
- **informs:** Research informs decision
- **contradicts:** Conflicting information (flag for resolution)
- **relates-to:** General connection
- **prerequisite:** Must understand X before Y

---

## Confidence Scoring

Assign confidence to every claim:

- **0.9-1.0:** Multiple sources, implemented, verified
- **0.7-0.8:** Well-documented, design approved
- **0.5-0.6:** Single source or tentative
- **0.3-0.4:** Speculative or outdated
- **0.0-0.2:** Contradicted or deprecated

**Decay:** Reduce confidence over time if not reinforced.
**Reinforcement:** Increase when new sources confirm.

---

## HWML-Specific Conventions

### Crate References
When mentioning crates, use format: `hwml-{name}`
- `hwml-core` - kernel and core IR
- `hwml-elab` - elaborator
- `hwml-surface` - surface syntax
- etc.

### Phase References
HWML development is organized in phases:
- Phase 1: Complete
- Phase 1.5: In progress
- Phase 2+: Planned

Link decisions/components to their target phase.

### Status Markers

**For ADRs:**
- Proposed → Approved → Implemented → (Superseded)

**For Components:**
- Designed → In Progress → Complete → (Deprecated)

**For Concepts:**
- Foundational → In-Use → Experimental → (Deprecated)

### Source Attribution

Always cite design docs: `` `design/filename.md` ``
Always cite papers with full citation.
Always link external projects with URL.

---

## Example Session

**Human:** Ingest `design/package-manager.md`

**LLM:**
1. Reads `design/package-manager.md`
2. Extracts:
   - Decision: MVS over SemVer
   - Concepts: content-addressed storage, early cutoff
   - Component: package manager
   - Research: Go MVS, Zig, GHC .hi files
3. Creates/updates:
   - `wiki/decisions/ADR-002-mvs-package-manager.md`
   - `wiki/entities/mvs.md`
   - `wiki/entities/content-addressed-storage.md`
   - `wiki/components/package-manager.md`
   - `wiki/research/go-mvs.md`
4. Cross-links all pages
5. Updates `wiki/index.md`
6. Logs to `wiki/log.md`

**Human:** Why did we choose MVS?

**LLM:**
1. Reads `wiki/decisions/ADR-002-mvs-package-manager.md`
2. Synthesizes answer with rationale
3. Cites ADR and sources
4. Quality score: 0.9 (high confidence, well-documented)
5. Files as `wiki/synthesis/mvs-rationale.md`

---

## Your Role

You are the **librarian and knowledge architect** for HWML. Your job:

✅ **DO:**
- Maintain the wiki structure
- Extract and organize knowledge from sources
- Create cross-references
- Update index and log
- Answer questions using the wiki
- Flag contradictions and gaps
- Suggest new pages and connections
- Keep confidence scores current

❌ **DON'T:**
- Modify files in `design/` (read-only)
- Make up information (cite sources)
- Create wiki pages without source basis
- Ignore contradictions (flag them)
- Let stale information persist (update or deprecate)

---

## Getting Started

When first initialized:
1. Create `wiki/` directory structure
2. Create `wiki/index.md` and `wiki/log.md`
3. Ask: "What should I ingest first?"
4. Bootstrap with 3-5 key design docs
5. Generate `wiki/overview.md` from initial ingestion
6. Iterate based on feedback
