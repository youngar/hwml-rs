# HWML Wiki System Proposal

**Created:** 2026-05-02  
**Status:** Proposal  
**Purpose:** Design a knowledge management system for HWML that preserves design decisions, rationales, and research context

---

## Problem Statement

HWML has accumulated 50+ design documents covering:
- Core language design (NbE, elaboration, universes, pattern matching)
- Architecture decisions (LCF kernel, Salsa integration, bidirectional typing)
- Implementation plans (package manager, LSP, CIRCT backend)
- Research artifacts (location design, debug info, async unification)
- Migration guides and comparisons

**Current challenges:**
1. **Scattered knowledge**: Design decisions are documented but connections between documents are implicit
2. **Lost context**: Why certain approaches were chosen over alternatives isn't always clear
3. **Difficult onboarding**: New contributors must read dozens of documents to understand the full picture
4. **Research references**: Papers, codebases, and discussions that informed decisions aren't systematically tracked
5. **Evolution tracking**: Hard to see how designs evolved, what was tried and abandoned

## Proposed Solution: HWML Design Wiki

Build an LLM-maintained wiki following the [LLM Wiki v2 pattern](./LLMWiki.md) tailored to HWML's needs.

### Architecture

```
hwml-rust/
├── design/              # Raw sources (existing docs, IMMUTABLE)
├── wiki/                # LLM-generated wiki (NEW)
│   ├── index.md         # Catalog of all wiki pages
│   ├── log.md           # Chronological record of wiki updates
│   ├── overview.md      # High-level HWML architecture overview
│   ├── entities/        # People, projects, libraries, concepts
│   │   ├── salsa.md
│   │   ├── nbe.md
│   │   ├── lcf-kernel.md
│   │   └── ...
│   ├── decisions/       # Architecture Decision Records (ADRs)
│   │   ├── ADR-001-bidirectional-typing.md
│   │   ├── ADR-002-mvs-package-manager.md
│   │   ├── ADR-003-async-elaboration.md
│   │   └── ...
│   ├── components/      # Major system components
│   │   ├── elaborator.md
│   │   ├── kernel.md
│   │   ├── package-manager.md
│   │   └── ...
│   ├── research/        # Research threads and references
│   │   ├── papers.md
│   │   ├── type-theory-foundations.md
│   │   ├── haskell-patterns.md
│   │   └── ...
│   ├── onboarding/      # Structured onboarding paths
│   │   ├── new-contributor-guide.md
│   │   ├── type-theory-primer.md
│   │   ├── codebase-map.md
│   │   └── ...
│   └── synthesis/       # Cross-cutting analyses
│       ├── design-evolution.md
│       ├── trade-offs.md
│       └── open-questions.md
└── WIKI.md              # Schema (instructions for LLM)
```

### Key Differences from Standard LLM Wiki

**Domain-specific adaptations:**

1. **Architecture Decision Records (ADRs)**: Each major design decision gets a structured page:
   - **Context**: What problem were we solving?
   - **Considered alternatives**: What other approaches did we evaluate?
   - **Decision**: What did we choose and why?
   - **Consequences**: Trade-offs, limitations, future implications
   - **Sources**: Which design docs, papers, or discussions informed this?
   - **Status**: Approved, Implemented, Superseded, etc.

2. **Research provenance tracking**: 
   - Papers cited in design docs extracted and cataloged
   - Connections to other languages/systems (GHC, Lean, OCaml, etc.)
   - Code snippets from external projects with attribution

3. **Implementation status tracking**:
   - Link wiki pages to actual implementation status
   - Cross-reference with phase plans (Phase 1, 1.5, 2, etc.)
   - Track what's designed vs. implemented vs. deprecated

4. **Technical concept explanations**:
   - NbE (Normalization by Evaluation)
   - Bidirectional typing
   - Pattern unification
   - Universe hierarchies
   - Each concept page includes: definition, how HWML uses it, references, related concepts

5. **Onboarding paths**:
   - "I want to understand the type system" → structured reading path
   - "I want to contribute to the elaborator" → prerequisite concepts + relevant docs
   - "I want to understand CIRCT integration" → focused subset of knowledge

### Operations

#### 1. Initial Bootstrap (One-time)

**Ingest existing design documents**: Process all 50+ docs in `design/` directory:
- Extract key concepts, decisions, and entities
- Build initial cross-reference graph
- Create entity pages (Salsa, NbE, CIRCT, etc.)
- Generate ADRs from existing decision documents
- Build index and initial overview

**LLM workflow:**
```bash
# Process all existing docs
for doc in design/*.md; do
  ingest $doc
done
```

The LLM will:
1. Read each document
2. Extract entities (concepts, libraries, people, decisions)
3. Create/update wiki pages
4. Add cross-references
5. Update index.md
6. Log to log.md

#### 2. Ongoing Maintenance

**When new design docs are added:**
- Auto-ingest (via git hook or manual command)
- Update affected entity pages
- Add/update ADRs if decisions are made
- Strengthen or challenge existing claims based on new information

**When questions are asked:**
- Answer using wiki (faster than re-reading raw docs)
- File valuable answers back into wiki as synthesis pages
- Example: "What were the trade-offs in choosing MVS over SemVer?" → generates comparison page

**Periodic lint/health checks:**
- Find contradictions between old and new design docs
- Identify orphaned concepts (mentioned but no dedicated page)
- Suggest missing cross-references
- Flag outdated status markers (e.g., "planned" features now implemented)

#### 3. Onboarding

**New contributor workflow:**
```
Contributor: "I want to understand how elaboration works"
LLM: Reads wiki/components/elaborator.md + related pages
     Returns: structured explanation + reading path through source docs
     Files session as: wiki/onboarding/elaboration-deep-dive.md
```

The wiki builds up common onboarding paths over time.

---

## Schema (WIKI.md)

The `WIKI.md` file at repository root will contain:

### Entity Types
- **Concept**: Technical concepts (NbE, unification, etc.)
- **Library**: External dependencies (Salsa, CIRCT, LALRPOP)
- **Decision**: Architecture decisions (ADR format)
- **Component**: Major system parts (kernel, elaborator, LSP)
- **Research**: Papers, external codebases, discussions
- **Phase**: Implementation phases
- **Person**: Contributors (optional)

### Relationship Types
- `uses`: Component uses library/concept
- `depends-on`: Component depends on component
- `implements`: Implementation realizes design
- `supersedes`: New decision replaces old
- `informs`: Research/paper informs decision
- `contradicts`: Conflicting information
- `relates-to`: General connection

### Quality Standards
- Every ADR must cite source documents
- Confidence scores for claims
- Date stamps for time-sensitive information
- Status markers: Proposed, Approved, Implemented, Deprecated

### Workflows

**Ingest source document:**
1. Parse document structure
2. Extract entities and relationships
3. Create new pages or update existing
4. Add cross-references
5. Update index
6. Log entry

**Answer query:**
1. Search index for relevant pages
2. Read and synthesize
3. Cite wiki pages
4. Score answer quality
5. If quality > threshold, file as synthesis page

**Lint:**
1. Check for orphans
2. Find contradictions
3. Verify cross-references
4. Flag stale status
5. Suggest consolidation opportunities

---

## Implementation Plan

### Phase 1: Bootstrap (Week 1)
- [ ] Create `wiki/` directory structure
- [ ] Create `WIKI.md` schema
- [ ] Ingest critical docs (ARCHITECTURE.md, package-manager.md, README.md)
- [ ] Generate initial index.md and overview.md
- [ ] Validate structure with sample queries

### Phase 2: Full Ingestion (Week 2)
- [ ] Batch ingest all design docs
- [ ] Generate entity pages
- [ ] Build cross-reference graph
- [ ] Create initial ADRs
- [ ] Generate onboarding guides

### Phase 3: Automation (Week 3)
- [ ] Git hooks for auto-ingest on new design docs
- [ ] Scheduled lint passes
- [ ] Query templates for common questions
- [ ] Integration with development workflow

### Phase 4: Enhancement (Ongoing)
- [ ] Add research paper tracking
- [ ] Link to implementation code
- [ ] Status synchronization (design vs. implementation)
- [ ] Collaboration features (if team grows)

---

## Example ADR Format

```markdown
# ADR-002: Minimum Version Selection for Package Manager

**Status:** Approved
**Date:** 2026-03-15
**Confidence:** 0.95

## Context

HWML needs a package manager for library dependencies. Must choose dependency resolution strategy.

## Alternatives Considered

1. **SemVer with SAT solver** (npm, cargo)
   - Pros: Flexible, finds "best" version
   - Cons: Non-deterministic, complex, silent downgrades

2. **Minimum Version Selection** (Go, Zig)
   - Pros: Deterministic, simple, reproducible
   - Cons: May not use latest compatible versions

3. **Manual pinning** (vendoring)
   - Pros: Complete control
   - Cons: Manual maintenance burden

## Decision

Use **Minimum Version Selection (MVS)** like Go.

**Rationale:**
- Reproducibility is critical for hardware compilation
- Determinism preferred over "optimal" versions
- Simpler implementation (Phase 3 feasible)
- Explicit `hwml update` gives control

## Consequences

**Positive:**
- Builds are reproducible
- No surprise version changes
- Simple mental model

**Negative:**
- Won't automatically use latest compatible versions
- Requires explicit updates

**Trade-offs:**
- Chosen reproducibility over convenience
- Hardware projects prioritize stability

## Sources

- `design/package-manager.md` (primary spec)
- Go MVS paper: https://research.swtch.com/vgo-mvs
- Zig package manager design
- Discussion: internal design review 2026-03-10

## Related

- [[ADR-001: Content-Addressed Artifacts]]
- [[wiki/entities/go-mvs.md]]
- [[wiki/components/package-manager.md]]
- Implemented in: Phase 3
```

---

## Benefits

1. **Faster onboarding**: New contributors read wiki overview + targeted paths instead of 50+ docs
2. **Preserved context**: Why decisions were made, what was considered, research basis
3. **Living documentation**: Auto-updates as new docs are added
4. **Better decisions**: Easy to see what's been tried, what works, what doesn't
5. **No manual maintenance**: LLM handles the bookkeeping

---

## Next Steps

1. **Review this proposal** - get feedback from team
2. **Create WIKI.md schema** - define entity types, formats, workflows
3. **Bootstrap with 5-10 key docs** - validate approach
4. **Iterate on structure** - adjust based on what works
5. **Full ingestion** - process all existing design docs
6. **Integrate into workflow** - make it part of development process

---

## Open Questions

- **Tooling**: Build custom search or use qmd/ripgrep?
- **Visualization**: Use Obsidian graph view or build custom?
- **Collaboration**: Single-user or multi-contributor?
- **Integration**: Link wiki to actual code implementation status?
- **Privacy**: Any sensitive design info to filter?
