# HWML Design Wiki - Implementation Summary

**Created:** 2026-05-02  
**Status:** Proposal Complete - Awaiting Approval  
**Next Step:** Review and decide whether to proceed with bootstrap

---

## What Was Created

A complete design for an LLM-maintained knowledge base system for HWML, consisting of:

### 1. Documentation Files

| File | Purpose | Audience |
|------|---------|----------|
| `design/LLMWiki.md` | The original pattern (Karpathy + agentmemory) | Understanding the concept |
| `design/WIKI-SYSTEM-PROPOSAL.md` | HWML-specific adaptation | Decision makers |
| `WIKI.md` (root) | Schema/instructions for LLM | The LLM agent |
| `design/WIKI-BOOTSTRAP-PLAN.md` | Step-by-step execution plan | Implementation |
| `design/WIKI-QUICK-START.md` | User guide and reference | Daily users |
| `design/EXAMPLE-ADR.md` | Concrete examples of wiki pages | Everyone |
| `design/WIKI-SUMMARY.md` | This file - overview | Decision makers |

### 2. Proposed Directory Structure

```
hwml-rust/
├── WIKI.md                    # LLM instructions/schema
└── wiki/                      # LLM-generated wiki (to be created)
    ├── index.md               # Catalog
    ├── log.md                 # Chronological history
    ├── overview.md            # HWML overview
    ├── entities/              # Concepts, libraries
    ├── decisions/             # ADRs (Architecture Decision Records)
    ├── components/            # System components
    ├── research/              # Papers, external projects
    ├── onboarding/            # Learning paths
    └── synthesis/             # Cross-cutting analyses
```

---

## Core Concept

**The Problem:**
- 50+ design documents in `design/` directory
- Scattered knowledge, implicit connections
- Lost context on "why" decisions were made
- Hard for new contributors to onboard
- Research references not systematically tracked

**The Solution:**
- LLM reads all design docs
- Extracts decisions, concepts, components, research
- Builds structured wiki with cross-references
- Maintains it automatically as new docs are added
- Answers questions using accumulated knowledge

**The Key Insight:**
Instead of RAG (retrieve and forget), build a **persistent, compounding artifact** that gets richer over time.

---

## What Makes It HWML-Specific

### Architecture Decision Records (ADRs)
Structured pages for every major decision:
- Context: What problem were we solving?
- Alternatives: What did we consider?
- Decision: What did we choose and why?
- Consequences: Trade-offs, limitations
- Sources: Which docs/papers informed this?

### Entity Types Tailored to Compiler Design
- **Concepts:** NbE, bidirectional typing, pattern unification
- **Components:** Kernel, elaborator, package manager
- **Libraries:** Salsa, CIRCT, LALRPOP
- **Research:** Papers, external projects (GHC, Lean, OCaml)
- **Phases:** Phase 1, 1.5, 2+ (implementation tracking)

### Cross-References to Actual Implementation
- Link ADRs to crates: `hwml-core`, `hwml-elab`, etc.
- Track status: Designed → In Progress → Complete
- Connect design docs to actual code

---

## Key Benefits

### For Onboarding (Primary Use Case)
**Current state:**
- New contributor reads README
- Overwhelmed by 50+ design docs
- Doesn't know where to start
- Spends days/weeks getting context

**With wiki:**
- New contributor reads `wiki/overview.md`
- Follows `wiki/onboarding/new-contributor-guide.md`
- Gets structured learning path based on interests
- Understands "why" through ADRs
- Onboards in hours/days instead of weeks

### For Development
**Common scenarios:**
- "Why did we choose MVS over SemVer?" → Read ADR-003
- "How does elaboration work?" → Read component page + linked concepts
- "What papers should I read about NbE?" → Check research page
- "Is feature X designed or implemented?" → Check status in wiki

### For Project Health
- **Institutional memory:** Never lose design rationale
- **Design evolution:** See how ideas changed over time
- **Onboard at scale:** As team grows, wiki scales
- **Knowledge compounding:** Each doc adds value to existing knowledge

---

## Implementation Effort

### Bootstrap (Week 1)
- **Time:** ~8 hours of LLM + human collaboration
- **Output:** Wiki structure + 5 key docs ingested + validation
- **Deliverable:** Proof of concept

### Full Ingestion (Week 1-2)
- **Time:** ~4 hours (mostly automated)
- **Output:** All 50+ docs processed, 100+ wiki pages
- **Deliverable:** Complete knowledge base

### Ongoing Maintenance
- **Time:** ~0 hours (automated)
- **Action:** Add "ingest new-doc.md" when creating design docs
- **Cost:** Minimal - LLM does the work

### Total Investment
- **Setup:** 12-16 hours over 2 weeks
- **Ongoing:** <5 minutes per new design doc
- **Payoff:** Immediate for onboarding, compounds over time

---

## Risk Assessment

### Low Risk
- **Non-destructive:** Never modifies design docs (read-only)
- **Version controlled:** All wiki changes in git
- **Reversible:** Can delete wiki and try again
- **Incremental:** Start small, expand if it works

### Possible Issues

1. **LLM makes mistakes in wiki pages**
   - Mitigation: Cites sources, easy to verify
   - Recovery: Regenerate or manually fix

2. **Wiki structure doesn't fit workflow**
   - Mitigation: Start with 5 docs, validate before full ingestion
   - Recovery: Adjust schema (WIKI.md) and regenerate

3. **Maintenance burden higher than expected**
   - Mitigation: Automation handles most of it
   - Recovery: Reduce scope (fewer entity types)

4. **Team doesn't use it**
   - Mitigation: Make it genuinely useful (good onboarding)
   - Recovery: No harm done, just extra documentation

### Rollback Plan
If it doesn't work:
1. Archive `wiki/` → `wiki-archive/`
2. Keep WIKI.md as design documentation
3. Extract useful ADRs as standalone docs
4. No harm to existing workflow

---

## Decision Points

### ✅ Recommend Proceeding If:
- Onboarding new contributors is a priority
- Design rationale preservation is important
- Team will grow (or might grow)
- You value institutional knowledge
- You like the LLM Wiki pattern

### ⚠️ Consider Alternatives If:
- Solo developer, no plans to expand
- Design docs rarely consulted
- Prefer manual curation
- Don't want LLM-generated content

### 🛑 Don't Proceed If:
- Not willing to spend 12-16 hours on setup
- Design docs contain sensitive information (though filtering is possible)
- Strong preference for traditional documentation only

---

## Next Steps

### If Approved

1. **Review:**
   - Read WIKI-SYSTEM-PROPOSAL.md (full design)
   - Read EXAMPLE-ADR.md (what output looks like)
   - Review WIKI.md schema (LLM instructions)

2. **Execute Bootstrap:**
   - Follow WIKI-BOOTSTRAP-PLAN.md
   - Start with 5 key documents
   - Validate structure and quality

3. **Iterate:**
   - Adjust based on feedback
   - Full ingestion if bootstrap succeeds
   - Integrate into development workflow

4. **Use:**
   - Reference in onboarding
   - Cite ADRs in code/PRs
   - Maintain as living documentation

### If Declined

**Still valuable:**
- WIKI.md as template for manual ADRs
- Entity type taxonomy (concepts, components, research)
- Idea of structured decision records

**Could extract:**
- Manual ADR template from EXAMPLE-ADR.md
- Onboarding structure ideas
- Design doc taxonomy

---

## Questions for Decision

1. **Does onboarding matter enough to invest 12-16 hours?**
2. **Do you like the ADR format for capturing decisions?**
3. **Would you consult the wiki when developing?**
4. **Is preserving design rationale important?**
5. **Any concerns about LLM-generated documentation?**

---

## Recommendation

**Proceed with bootstrap (Phase 1).**

**Rationale:**
- Low risk (non-destructive, version controlled)
- High potential value (onboarding, institutional knowledge)
- Reasonable investment (~8 hours to validate)
- Easy to rollback if it doesn't work
- HWML is complex enough to benefit from this

**Validation criteria after bootstrap:**
- Can answer "why?" questions correctly
- ADRs accurately reflect design decisions
- Wiki structure makes sense for HWML
- Would actually use this for onboarding

If bootstrap succeeds → proceed to full ingestion.  
If bootstrap fails → extract useful patterns, archive wiki.

---

## Contact

For questions about the wiki system design:
- Read: `design/WIKI-QUICK-START.md`
- Examples: `design/EXAMPLE-ADR.md`
- Full proposal: `design/WIKI-SYSTEM-PROPOSAL.md`

Ready to begin: `design/WIKI-BOOTSTRAP-PLAN.md`
