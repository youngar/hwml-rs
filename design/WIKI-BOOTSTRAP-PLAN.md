# HWML Wiki Bootstrap Plan

**Created:** 2026-05-02  
**Status:** Ready to Execute  
**Purpose:** Step-by-step plan to bootstrap the HWML Design Wiki

---

## Prerequisites

✅ **Completed:**
- [x] WIKI.md schema created
- [x] WIKI-SYSTEM-PROPOSAL.md written
- [x] Understanding of LLM Wiki pattern

⏳ **Before starting:**
- [ ] Review and approve WIKI-SYSTEM-PROPOSAL.md
- [ ] Confirm `wiki/` directory structure
- [ ] Decide on initial document set

---

## Bootstrap Phases

### Phase 0: Setup (5 minutes)

**Create directory structure:**
```bash
mkdir -p wiki/{entities,decisions,components,research,onboarding,synthesis}
```

**Create foundational files:**
- `wiki/index.md` (empty catalog)
- `wiki/log.md` (empty log)

**First log entry:**
```markdown
## [2026-05-02] bootstrap | Wiki initialization

**Status:** Starting  
**Goal:** Process first 5 key design documents  
**Structure:** Created directory layout per WIKI.md schema
```

---

### Phase 1: Critical Documents (Day 1)

**Ingest priority order:**

#### 1. ARCHITECTURE.md ⭐⭐⭐
**Why first:** Defines core architectural principles (LCF kernel, bidirectional typing)

**Expected outputs:**
- `wiki/decisions/ADR-001-lcf-kernel.md`
- `wiki/decisions/ADR-002-bidirectional-typing.md`
- `wiki/entities/lcf-pattern.md`
- `wiki/entities/bidirectional-typing.md`
- `wiki/components/kernel.md`

#### 2. README.md (root) ⭐⭐⭐
**Why:** High-level overview, project purpose

**Expected outputs:**
- `wiki/overview.md`
- Update entities: dependent-types, metaprogramming, circt

#### 3. package-manager.md ⭐⭐
**Why:** Major design document with multiple decisions

**Expected outputs:**
- `wiki/decisions/ADR-003-mvs-package-manager.md`
- `wiki/decisions/ADR-004-content-addressed-artifacts.md`
- `wiki/components/package-manager.md`
- `wiki/entities/mvs.md`
- `wiki/entities/content-addressed-storage.md`
- `wiki/research/go-mvs.md`
- `wiki/research/ghc-patterns.md`

#### 4. design/README.md ⭐⭐
**Why:** Meta-document about design docs themselves

**Expected outputs:**
- `wiki/onboarding/design-docs-guide.md`
- Cross-references to package-manager entities

#### 5. NbE-IMPLEMENTATION-PLAN.md ⭐
**Why:** Key type system component

**Expected outputs:**
- `wiki/entities/nbe.md`
- `wiki/components/nbe-evaluator.md`
- Links to kernel, type-checking

---

### Phase 2: Validation (Day 1 continued)

**After ingesting first 5 docs:**

#### Test Queries

1. **Q:** "What is HWML?"  
   **Expected:** Synthesize from overview, README, ARCHITECTURE

2. **Q:** "Why did we choose MVS for package management?"  
   **Expected:** Read ADR-003, cite rationale and alternatives

3. **Q:** "How does the LCF kernel work?"  
   **Expected:** Read ADR-001, kernel component page, cite ARCHITECTURE.md

4. **Q:** "What is NbE and why do we use it?"  
   **Expected:** Read entities/nbe.md, cite implementation plan

#### Lint Check

Run first lint:
```
lint
```

**Expected findings:**
- Some orphaned concepts (mentioned but no page yet)
- Some missing cross-references
- This is NORMAL at bootstrap - will improve with more docs

#### Review

Human reviews:
- `wiki/index.md` - does structure make sense?
- Sample ADR - is format correct?
- Sample entity page - appropriate depth?
- Sample component page - useful information?

**Iterate:** Adjust WIKI.md schema if needed, re-ingest if necessary.

---

### Phase 3: Batch Ingestion (Week 1)

**Once validated, ingest remaining docs in batches:**

#### Batch A: Type System (5 docs)
- `elaboration.md`
- `universes.md`
- `unification.md`
- `pattern-matching.md`
- `kernel-judgements.md`

**Expected:** Rich concept graph for type theory

#### Batch B: Implementation Status (5 docs)
- `PHASE1-COMPLETE.md`
- `PHASE1.5-PLAN.md`
- `LET_IMPLEMENTATION_FINAL.md`
- `nbe-phase1-implementation.md`
- `ELABORATOR_PROGRESS.md` (root)

**Expected:** Clear implementation status tracking

#### Batch C: Research & Comparisons (5 docs)
- `lsp-object-file-research.md`
- `nbe-vs-legacy-comparison.md`
- `COMPARISON-SUMMARY.md`
- `location-design-comparison.md`
- `debug-info-research.md`

**Expected:** Rich research pages, external project references

#### Batch D: Technical Deep Dives (remaining docs)
- All `2ltt-*.md` files
- Location-related docs
- Async unification
- etc.

**Strategy:** These can be ingested as-needed rather than all at once.

---

### Phase 4: Onboarding Generation (Week 1 end)

**Create onboarding paths from accumulated knowledge:**

#### Auto-generate:
1. `wiki/onboarding/new-contributor-guide.md`
   - From: overview + key ADRs + component summaries

2. `wiki/onboarding/type-system-primer.md`
   - From: NbE, bidirectional typing, elaboration concepts

3. `wiki/onboarding/codebase-map.md`
   - From: component pages + crate structure

4. `wiki/onboarding/contributing-to-elaborator.md`
   - From: elaborator component + related concepts + implementation status

**Human review:** These need human validation since they're synthesis.

---

### Phase 5: Integration (Week 2)

#### Git Hooks (optional)
Create `.git/hooks/pre-commit` to suggest wiki updates:
```bash
#!/bin/bash
# Check if any design/*.md files changed
if git diff --cached --name-only | grep "^design/.*\.md$"; then
  echo "Design docs changed. Consider: ingest <file>"
fi
```

#### Scheduled Maintenance
Add to development routine:
- Weekly lint pass
- Monthly consolidation review
- Update implementation status quarterly

#### Query Templates
Document common queries:
```markdown
# Common Wiki Queries

- "What design docs relate to {topic}?"
- "Why did we choose {X} over {Y}?"
- "What's the status of {feature}?"
- "How does {component} work?"
- "What are the open questions for {topic}?"
```

---

## Success Metrics

### After Phase 1 (Day 1):
- [ ] 5 docs ingested
- [ ] 10+ wiki pages created
- [ ] Index structure validated
- [ ] Sample queries work correctly
- [ ] First lint pass completed

### After Phase 3 (Week 1):
- [ ] 50+ design docs ingested
- [ ] 100+ wiki pages created
- [ ] Cross-reference graph dense
- [ ] Onboarding paths generated
- [ ] Can answer "why?" questions with confidence

### After Phase 5 (Week 2):
- [ ] Wiki integrated into development workflow
- [ ] New contributors use onboarding guides
- [ ] Design decisions reference ADRs
- [ ] Implementation status synchronized
- [ ] Wiki provides value in daily work

---

## Rollback Plan

If bootstrap doesn't work as expected:

1. **Keep WIKI.md schema** - useful documentation regardless
2. **Archive wiki/** - move to `wiki-experimental/`
3. **Adjust approach:**
   - Simpler structure?
   - Different entity types?
   - Manual curation instead of auto-generation?
4. **Try again** with lessons learned

No harm done - design docs remain untouched.

---

## Next Action

**Ready to start?**

```
Human: "Create the wiki directory structure and ingest ARCHITECTURE.md"

LLM: 
1. mkdir -p wiki/{entities,decisions,components,research,onboarding,synthesis}
2. Create wiki/index.md and wiki/log.md
3. Read design/ARCHITECTURE.md
4. Extract entities, decisions, components
5. Create wiki pages
6. Update index
7. Log entry
8. Report completion
```

Let's begin!
