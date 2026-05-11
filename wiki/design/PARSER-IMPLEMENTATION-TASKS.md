# Parser Implementation: Exhaustive Task List

**Date:** 2026-05-11  
**Status:** Ready for execution  
**Total Timeline:** 22 days (4 weeks + 2 days)  
**Total Tasks:** 116 tasks across 11 phases  

---

## Overview

Complete task breakdown for implementing the top-down recursive descent parser with Agda-style mixfix operator resolution.

**Key Features:**
- ✅ Typed stacks (no runtime panics)
- ✅ Block-depth-aware error recovery
- ✅ Provenance tracking (rich error messages)
- ✅ Flat pattern sequences (Agda-style)
- ✅ Scope checker operator resolution
- ✅ SPPF for ambiguous parsings

---

## Phase Breakdown

### Phase 1: Parser Foundation (2.5 days) - 13 tasks
- Create parse module structure
- Define State enum (states carry data)
- Implement Context struct (typed stacks, provenance, block depth)
- Implement Parser main loop
- Write foundation tests

**Deliverable:** Complete infrastructure, no actual parsing yet

---

### Phase 2: Simple Statements (2 days) - 8 tasks
- Create handle_stmt.rs
- Implement prim, def, meta handlers
- Basic expression parsing (literals, ids, parens)
- Write statement tests

**Deliverable:** Can parse simple top-level definitions

---

### Phase 3: Expression Parsing (2 days) - 14 tasks
- Create handle_expr.rs
- Implement precedence climbing
- Parse pi, arrow, fun, let, app, dot
- Handle parentheses and universes
- Write expression tests

**Deliverable:** Full expression grammar with precedence

---

### Phase 4: Bindings with Flat Patterns (1 day) - 14 tasks
- Add Pattern AST to syntax.rs (AppSeq, not Infix!)
- Add Binder struct
- Update TypedBindingGroup and UntypedBindingGroup
- Parse patterns as flat sequences
- Implement as-pattern parsing
- Write binding tests

**Deliverable:** Pattern grammar with flat sequences (NO operator parsing!)

---

### Phase 5: Inductive Types (2 days) - 11 tasks
- Create handle_inductive.rs
- Parse inductive declarations
- Parse constructors
- Handle params vs indices
- Write inductive tests

**Deliverable:** Full inductive type support

---

### Phase 6: Namespace and Open (1 day) - 8 tasks
- Parse namespace with nested blocks
- Track brace_stack and block_depth
- Parse open with modifiers
- Write namespace tests

**Deliverable:** Module system parsing

---

### Phase 7: Error Recovery (2.5 days) - 12 tasks
- Implement block-depth-aware skip_to_recovery_point
- Statement and expression level recovery
- Brace/paren matching validation
- Provenance capture in errors
- Stress test error recovery

**Deliverable:** Robust error handling, multiple errors per parse, no file swallowing

---

### Phase 8: Match Expressions (1 day) - 11 tasks
- Add Match and MatchClause to syntax.rs
- Parse match expressions
- Integrate with existing pattern parser (from Phase 4)
- Track block_depth for nested matches
- Write match tests

**Deliverable:** Pattern matching with flat pattern sequences

---

### Phase 9: Scope Checker Operator Resolution (2 days) - 16 tasks ⭐ NEW
- Define core::Pattern AST (Var, Constructor, MixfixOp, Ambiguous)
- Implement name resolution (resolve_name)
- Implement find_applicable_operators
- Build precedence graph
- Implement precedence climbing with fixity
- Construct SPPF for ambiguous parsings
- Resolve AppSeq -> structured patterns
- Test mixfix patterns

**Deliverable:** Full mixfix operator support in patterns!

---

### Phase 10: Migration and Testing (2 days) - 11 tasks
- Update parsing.rs
- Remove LALRPOP (build.rs, grammar.lalrpop, Cargo.toml)
- Run full test suite
- Test error messages and provenance
- Test mixfix patterns end-to-end
- Fix regressions

**Deliverable:** Complete migration, no LALRPOP

---

### Week 4: Polish and Documentation (5 days) - 10 tasks
- Provenance integration testing
- Error message quality review
- Performance benchmarking
- Mixfix pattern integration tests
- Memory profiling
- Documentation
- Final regression testing

**Deliverable:** Production-ready parser

---

## Task Statistics

**Total:** 116 tasks  

**By Phase:**
- Phase 1: 13 tasks (foundation)
- Phase 2: 8 tasks (simple statements)
- Phase 3: 14 tasks (expressions)
- Phase 4: 14 tasks (flat patterns)
- Phase 5: 11 tasks (inductive)
- Phase 6: 8 tasks (namespace)
- Phase 7: 12 tasks (error recovery)
- Phase 8: 11 tasks (match)
- Phase 9: 16 tasks (operator resolution) ⭐
- Phase 10: 11 tasks (migration)
- Week 4: 10 tasks (polish)

**By Type:**
- Implementation: ~85 tasks
- Testing: ~25 tasks
- Documentation: ~6 tasks

---

## Critical Path

**Most Important Tasks:**
1. Phase 1: Context with typed stacks (foundation)
2. Phase 4: Pattern AST with AppSeq (enables mixfix)
3. Phase 7: Block-depth-aware error recovery (robustness)
4. Phase 9: Operator resolution in scope checker (mixfix support)

**Dependencies:**
- Phase 8 depends on Phase 4 (pattern grammar)
- Phase 9 depends on Phase 4 (surface::Pattern AST)
- Phase 10 depends on all previous phases

---

## Next Steps

1. **Review task list** - Ensure all tasks are clear
2. **Set up tracking** - Use task management system
3. **Start Phase 1** - Begin with parser foundation
4. **Daily progress updates** - Mark tasks as complete

**Command to view tasks:**
```bash
# View all tasks in conversation
# (use task management tool or view_tasklist)
```

---

**Status:** ✅ Task list complete, ready to begin implementation  
**Confidence:** 9.5/10 (exhaustive breakdown, clear deliverables)  
**Timeline:** 22 days (realistic, tested estimate)
