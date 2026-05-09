# NbE Implementation Plan: Executive Summary

## What We're Building

A **Normalization by Evaluation (NbE)** elaborator implementing Jon Sterling's "Fuss-free universe hierarchies" with a Tarski-style separation between semantic types and syntactic codes.

## Why This Architecture?

1. **Simplicity:** Unifier goes from ~2,500 lines to ~200 lines
2. **Correctness:** Pattern unification firewall prevents ill-typed solutions
3. **Extensibility:** Adding new types only requires updating 2 enums
4. **User Experience:** Users rarely write universe levels (Sterling's philosophy)
5. **State-of-the-Art:** This is the architecture used by `cooltt` and modern proof assistants

## The Core Innovation: 4 Quadrants

We split along **two axes**:

```
                TERMS (Data)           TYPES (Classifiers)
              ─────────────────       ─────────────────────
SYNTAX     │  Syntax<'db>          │  TySyntax<'db>
(AST)      │  - Codes for types    │  - Top-level types
           │  - Unevaluated        │  - Unevaluated
           │                       │
SEMANTIC   │  Value<'db>           │  Ty<'db>
(Eval)     │  - Evaluated codes    │  - Evaluated types
           │  - WHNF               │  - What unifier sees
```

**The Bridge:** `Ty::El(Value)` decodes type codes into semantic types.

## Timeline: 2 Weeks

### Week 1: Core Engine
- **Days 1-2:** Define the 4 quadrants (Syntax, Value, TySyntax, Ty)
- **Days 3-4:** Implement eval and quote
- **Days 5-7:** Implement unification with pattern unification

### Week 2: Elaboration & Integration
- **Days 8-10:** Implement bidirectional elaboration (check/synth)
- **Days 11-12:** Wire up CLI and error reporting
- **Days 13-14:** Remove old code, run tests, celebrate 🎉

## Key Design Decisions

1. **No Universe Polymorphism:** Only concrete levels (Type 0, Type 1, ...)
2. **Hardware Arrows are Top-Level:** `HArrow` is a `Ty`, not a code
3. **Single-Threaded Async:** Keep `Rc<RefCell<>>`, no `Arc`/`Mutex`
4. **No Salsa Interning:** `Syntax` and `Ty` are ephemeral, not interned
5. **Closures Use Environments:** Standard NbE approach

## The Firewall: Pattern Unification

When solving `?M x y = rhs`:

1. **Inversion Check:** Spine must be distinct variables
2. **Occurs Check:** `?M` must not occur in `rhs`
3. **Scope Check:** `rhs` must only reference spine variables
4. **Assignment:** If all pass, assign `?M := λx. λy. rhs`

**No circular dependency:** We never call `check` from `unify`.

## Files to Create

```
crates/hwml-core/src/nbe/
  ├── mod.rs
  ├── syntax.rs        # Quadrant 1
  ├── value.rs         # Quadrant 2
  ├── ty.rs            # Quadrants 3 & 4
  ├── eval.rs
  └── quote.rs

crates/hwml-elab/src/nbe/
  ├── mod.rs
  ├── unify.rs
  └── elaborate.rs
```

## Migration Strategy

1. Create new `nbe/` modules alongside old code
2. Migrate elaborator first (smallest)
3. Migrate unifier (rewrite from scratch)
4. Update CLI to use new pipeline
5. Delete old `syn/` and `val/` modules

## Success Metrics

- [ ] Can elaborate `fun x => x` to `Syntax::Lam(...)`
- [ ] Can unify `Ty::Pi(A, B)` with `Ty::Pi(C, D)`
- [ ] Can solve `?M x y = f x y` to `?M = f`
- [ ] Occurs check prevents `?M = ?M -> Nat`
- [ ] Automatic `El` insertion works
- [ ] CLI can elaborate example programs
- [ ] All tests pass

## Next Steps

1. **Review** `design/nbe-architecture.md` (full specification)
2. **Review** `design/nbe-quick-reference.md` (cheat sheet)
3. **Answer** the 4 open questions in the architecture doc
4. **Start** Phase 1: Create the data structures

## Open Questions (Need Answers)

1. **Inductive Declarations:** How to represent in global environment?
2. **Case Return Types:** Add to `Syntax::Case` or infer?
3. **Metavariable Substitutions:** Store as `Syntax` or `Value`?
4. **Transparency:** How to control constant unfolding?

## Resources

- **Full Spec:** `design/nbe-architecture.md` (1,648 lines)
- **Quick Reference:** `design/nbe-quick-reference.md` (150 lines)
- **This Plan:** `design/NbE-IMPLEMENTATION-PLAN.md` (you are here)

## The Bottom Line

This is a **total rewrite** of the core elaborator, but it will result in:
- **Simpler code** (less than half the lines)
- **Fewer bugs** (firewall prevents ill-typed terms)
- **Better UX** (users don't fight universe levels)
- **Easier maintenance** (clean separation of concerns)

**Are you ready to build the future?** 🚀

