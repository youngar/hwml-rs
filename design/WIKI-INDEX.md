# HWML Design Wiki Documentation - Index

**Created:** 2026-05-02  
**Purpose:** Navigation guide for all wiki-related documentation

---

## 📚 Quick Navigation

### 🎯 I Want To...

**Understand what this is:**
→ Start with `WIKI-QUICK-START.md`

**Make a decision about implementing it:**
→ Read `WIKI-SUMMARY.md`

**See what wiki pages would look like:**
→ Check `EXAMPLE-ADR.md`

**Understand the pattern/philosophy:**
→ Read `LLMWiki.md`

**See visual examples and diagrams:**
→ View `WIKI-VISUAL-GUIDE.md`

**Get full technical details:**
→ Read `WIKI-SYSTEM-PROPOSAL.md`

**Actually implement it:**
→ Follow `WIKI-BOOTSTRAP-PLAN.md`

**Understand LLM instructions:**
→ Read `../WIKI.md` (root directory)

---

## 📄 Document Guide

### Entry Points (Start Here)

#### `WIKI-QUICK-START.md` ⭐⭐⭐
- **Audience:** Everyone
- **Length:** 5-10 minutes
- **Purpose:** Quick overview, commands, benefits
- **When:** First thing to read

#### `WIKI-SUMMARY.md` ⭐⭐⭐
- **Audience:** Decision makers
- **Length:** 10 minutes
- **Purpose:** Complete overview for go/no-go decision
- **When:** Before approving implementation

#### `WIKI-VISUAL-GUIDE.md` ⭐⭐
- **Audience:** Visual learners
- **Length:** 10 minutes
- **Purpose:** Diagrams and workflow illustrations
- **When:** Want to understand structure visually

### Foundation Documents

#### `LLMWiki.md` ⭐⭐
- **Audience:** Those who want deep understanding
- **Length:** 30 minutes
- **Purpose:** Original pattern by Karpathy + agentmemory extensions
- **When:** Want to understand the theoretical foundation

#### `WIKI-SYSTEM-PROPOSAL.md` ⭐
- **Audience:** Implementers, reviewers
- **Length:** 20 minutes
- **Purpose:** Full HWML-specific design
- **When:** Need all technical details

### Implementation

#### `../WIKI.md` (root directory) ⭐⭐⭐
- **Audience:** The LLM agent
- **Length:** Reference document
- **Purpose:** Schema, templates, workflows, conventions
- **When:** Actually running the wiki system

#### `WIKI-BOOTSTRAP-PLAN.md` ⭐⭐
- **Audience:** Person implementing bootstrap
- **Length:** Step-by-step guide
- **Purpose:** Execution plan with phases and validation
- **When:** Ready to build the wiki

### Examples

#### `EXAMPLE-ADR.md` ⭐⭐
- **Audience:** Everyone
- **Length:** 15 minutes
- **Purpose:** Concrete examples of generated wiki pages
- **When:** Want to see what output looks like

---

## 🗺️ Reading Paths

### Path 1: Quick Evaluation (20 minutes)
For: "Should we do this?"

1. `WIKI-QUICK-START.md` (5 min)
2. `WIKI-VISUAL-GUIDE.md` - skim diagrams (5 min)
3. `EXAMPLE-ADR.md` - see examples (5 min)
4. `WIKI-SUMMARY.md` - decision points (5 min)

**Outcome:** Enough information to decide yes/no

### Path 2: Deep Understanding (60 minutes)
For: "I want to fully understand this"

1. `WIKI-QUICK-START.md` (5 min)
2. `LLMWiki.md` (30 min)
3. `WIKI-SYSTEM-PROPOSAL.md` (20 min)
4. `WIKI.md` (root) - skim (5 min)

**Outcome:** Complete understanding of pattern and design

### Path 3: Implementation (2-4 hours)
For: "Let's build this"

1. `WIKI-QUICK-START.md` (5 min)
2. `WIKI-BOOTSTRAP-PLAN.md` (10 min)
3. Execute Phase 0-1 (1-2 hours)
4. Reference `WIKI.md` as needed
5. Validate and iterate (1-2 hours)

**Outcome:** Working wiki with first documents ingested

### Path 4: Daily Usage (ongoing)
For: "I need to use the wiki"

- Ingest docs: Use commands from `WIKI-QUICK-START.md`
- Ask questions: Natural language queries
- Check health: Periodic lint
- Reference: `WIKI.md` for conventions

**Outcome:** Productive daily use

---

## 📊 Document Comparison

| Document | Purpose | Length | Technical | Actionable | Visual |
|----------|---------|--------|-----------|------------|--------|
| WIKI-QUICK-START | Overview | Short | Low | High | Medium |
| WIKI-SUMMARY | Decision | Medium | Low | Low | Low |
| WIKI-VISUAL-GUIDE | Understanding | Medium | Low | Low | High |
| LLMWiki.md | Foundation | Long | Medium | Low | Low |
| WIKI-SYSTEM-PROPOSAL | Design | Long | High | Medium | Low |
| WIKI.md | Schema | Reference | High | High | Low |
| WIKI-BOOTSTRAP-PLAN | Implementation | Medium | Medium | High | Medium |
| EXAMPLE-ADR | Examples | Medium | Medium | Low | Medium |

---

## 🔍 Find By Topic

### Architecture & Design
- Overall system: `WIKI-SYSTEM-PROPOSAL.md`
- Directory structure: All documents
- Entity types: `WIKI.md`
- Workflows: `WIKI.md`

### Usage
- Commands: `WIKI-QUICK-START.md`
- Daily workflow: `WIKI-QUICK-START.md`
- Query examples: `WIKI-VISUAL-GUIDE.md`

### Implementation
- Bootstrap steps: `WIKI-BOOTSTRAP-PLAN.md`
- LLM instructions: `WIKI.md`
- Validation: `WIKI-BOOTSTRAP-PLAN.md`

### Examples
- ADR format: `EXAMPLE-ADR.md`
- Entity page: `EXAMPLE-ADR.md`
- Workflows: `WIKI-VISUAL-GUIDE.md`

### Philosophy
- Pattern origin: `LLMWiki.md`
- Why this works: `LLMWiki.md`
- Rationale: `WIKI-SYSTEM-PROPOSAL.md`

---

## ✅ Checklist: What To Read

### If you're deciding whether to implement:
- [ ] `WIKI-QUICK-START.md`
- [ ] `WIKI-SUMMARY.md`
- [ ] `EXAMPLE-ADR.md`

### If you're implementing:
- [ ] `WIKI-BOOTSTRAP-PLAN.md`
- [ ] `WIKI.md` (root)
- [ ] `EXAMPLE-ADR.md` (for reference)

### If you're using an existing wiki:
- [ ] `WIKI-QUICK-START.md`
- [ ] `WIKI.md` (root) - for conventions

### If you're curious about the pattern:
- [ ] `LLMWiki.md`
- [ ] `WIKI-SYSTEM-PROPOSAL.md`

---

## 🎓 Learning Objectives

After reading the appropriate docs, you should be able to:

### After Quick Start path:
- Explain what the wiki system is
- Understand the benefits
- Know how to use it
- Decide if it's worth pursuing

### After Deep Understanding path:
- Explain the LLM Wiki pattern
- Understand why it works
- Design variations for other domains
- Critique and improve the design

### After Implementation path:
- Bootstrap the wiki
- Ingest documents
- Run queries
- Maintain the system

---

## 📝 Status Tracking

**As of 2026-05-02:**

| Phase | Status | Documents |
|-------|--------|-----------|
| Documentation | ✅ Complete | All 8 files created |
| Review | ⏳ Pending | Awaiting approval |
| Bootstrap | 📋 Planned | WIKI-BOOTSTRAP-PLAN.md ready |
| Implementation | 🔜 Not Started | Waiting for approval |
| Integration | 🔜 Not Started | Post-bootstrap |

---

## 🤝 Contributing

If adding to this documentation:

1. Keep this index updated
2. Add cross-references in documents
3. Update reading paths if structure changes
4. Maintain the comparison table

---

## ❓ Still Have Questions?

- Technical details → `WIKI-SYSTEM-PROPOSAL.md`
- Usage questions → `WIKI-QUICK-START.md`
- Philosophy → `LLMWiki.md`
- Implementation → `WIKI-BOOTSTRAP-PLAN.md`
- Everything else → Ask the LLM!

---

## 🚀 Ready to Start?

**If approved:**
```
1. Read: WIKI-BOOTSTRAP-PLAN.md
2. Execute: Phase 0 (setup)
3. Execute: Phase 1 (first 5 docs)
4. Validate: Run test queries
5. Decide: Continue or iterate
```

**If exploring:**
```
1. Read: WIKI-QUICK-START.md
2. Review: EXAMPLE-ADR.md
3. Consider: Benefits for your use case
```
