# Implicit Arguments Research Summary

**Date:** 2026-05-13  
**Status:** Research complete, ready for implementation

---

## TL;DR

✅ **Decision:** Implement **Dynamic Order Elaboration (DOE)** for implicit arguments  
✅ **Complexity:** ~150 lines of code overhead  
✅ **No core syntax changes required**  
✅ **Best practical solution** (simpler than FCIF, stronger than Quick Look)

---

## Your Questions Answered

### 1. Core AST Representation

**Current state:**
```rust
// Syntax (no Icit yet)
PiCode(RcSyntax, BindingSyntax)           // Π-type
Lambda { body: BindingSyntax }            // λ
Application { function, argument }        // application
```

**After adding Icit:**
```rust
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Icit {
    Explicit,
    Implicit,
}

// Updated Syntax
PiCode(RcSyntax, Icit, BindingSyntax)     // Π-type with visibility
Lambda { body: BindingSyntax }             // λ (Icit in binding)
Application { function, argument, icit }   // application with visibility
```

**Memory management:**
- Uses `Rc<Syntax<'db>>` (reference counting)
- Salsa `'db` lifetime (NOT tracked structs)
- Adding Icit = **just another field**, no interning concerns
- **Trivial change**

### 2. NbE Value Domain

**Current Spine:**
```rust
pub struct Spine<'db>(pub Vec<Eliminator<'db>>);

pub enum Eliminator<'db> {
    Application(Application<'db>),  // ← Add Icit here
    Case(Case<'db>),
}

pub struct Application<'db> {
    pub argument: Normal<'db>,  // ← Add: pub icit: Icit
}
```

**Current Neutrals:**
```rust
pub struct Rigid<'db> {
    pub ty: RcValue<'db>,
    pub head: Variable,
    pub spine: Spine<'db>,  // Vec<Eliminator>
}

pub struct Flex<'db> {
    pub ty: RcValue<'db>,
    pub head: MetaVariable<'db>,
    pub spine: Spine<'db>,  // Vec<Eliminator>
}
```

**After adding Icit:**
- Each `Application` eliminator stores `icit: Icit`
- Spine becomes `Vec<Eliminator>` where `Eliminator::Application` has Icit
- **No Vec<(Eliminator, Icit)>** - Icit goes inside Application

### 3. Unification and Metavariables

**Current state:**
```rust
// Elaborator metavariables
pub struct SolverState<'db> {
    metas: HashMap<MetaId, MetaEntry<'db>>,  // ← substitution table
    constraints: HashMap<ConstraintId, ConstraintEntry<'db>>,
    // ...
}

pub struct MetaEntry<'db> {
    pub id: MetaId,
    pub ty: RcTy<'db>,
    pub solution: Option<MetaSolution<'db>>,  // ← solved value
    pub kind: MetaKind,  // Term or UniverseLevel
}

// Core metavariables
pub struct MetaVariableId {
    pub local_index: u16,  // Simple index
}
```

**Unification algorithm:**
- **Pattern unification** exists (`crates/hwml-core/src/pattern_unify.rs`)
- **Structural equality** with δ-reduction (`crates/hwml-core/src/equal.rs`)
- Unfolds transparent definitions before comparing

**Icit matching strictness:**
- ✅ **Recommend: Strict matching** - `{Explicit, arg} ≠ {Implicit, arg}`
- Insertion happens during **elaboration**, not unification
- Keep unification simple and predictable

### 4. Hardware Generation

**Critical finding:** ✅ **Implicit arguments are ERASED after type checking!**

```rust
// Hardware lowering (crates/hwml-core/src/lower.rs)
pub fn saturate_value(...) {
    // Beta-reduces ALL lambdas (implicit or explicit)
    // Hardware sees only saturated, concrete applications
}

// CIRCT translation (crates/hwml-circt/src/translate_new.rs)
pub fn translate_module(...) {
    // Operates on post-elaboration core IR
    // All implicit args already beta-reduced away
    // Wire generation UNAFFECTED
}
```

**Conclusion:**
- Icit is **type-checking time only**
- Hardware backend needs **zero changes**
- All lambdas erased during lowering to hardware

---

## The DOE Algorithm

### What is DOE?

**Dynamic Order Elaboration** - postpone checking when insertion is ambiguous.

**Invented by:** András Kovács (elaboration-zoo, 2020)

### How it works:

```rust
fn check(term, ty) {
    match ty.head() {
        // Known implicit function → insert lambda
        PiCode(_, Implicit, _) => insert_lambda_and_check(),
        
        // Known explicit function → no insertion
        PiCode(_, Explicit, _) => check_without_insertion(),
        
        // Meta-headed (unknown!) → POSTPONE
        Flex(meta_id, spine) => {
            let placeholder = fresh_meta(ty);
            postponed_checks.push(PostponedCheck {
                term, ty, placeholder, blocked_on: meta_id
            });
            return placeholder;  // Promise to fill in later
        }
    }
}

fn solve_meta(meta_id, solution) {
    // Solve the meta
    metas[meta_id] = Some(solution);
    
    // Retry all checks blocked on this meta
    for check in blocked_on[meta_id] {
        let ty_forced = force(check.ty);  // Substitute solved meta
        
        // Now we know the type - actually check!
        if !ty_forced.is_meta_headed() {
            let result = check(check.term, ty_forced);
            unify(check.placeholder, result);  // Fill the promise
        }
    }
}

fn finish_file() {
    // Process remaining postponed checks
    // Assume no insertion (guess explicit)
    for check in postponed_checks {
        let result = check_explicit(check.term, check.ty);
        unify(check.placeholder, result);
    }
}
```

### Key insight: Placeholder Metas

**Why critical:**
- Without: postponing creates cascading blockage
- With: downstream code can unify with placeholder
- Placeholder = **promise** filled in later

**Example:**
```
let foo : ?M = ?P  -- ?P = placeholder for postponed check
... code that uses foo ...
... unify ?M with Bool ...  -- Works! ?P can be used
-- Later: actually check the term, solve ?P
```

---

## Implementation Roadmap

### Phase 1: Icit Infrastructure (Week 1)

1. Add `Icit` enum to `crates/hwml-core/src/common.rs`
2. Update `Syntax`: `PiCode`, `Lambda`, `Application`
3. Update `Value`: `PiCode`, `Lambda`, `Eliminator::Application`
4. Update parser: `{x : A} → B` syntax
5. Update printer: show `{A}` vs `(A)`
6. Update equality checking: strict Icit matching

### Phase 2: Basic Insertion (Week 2)

1. Implement insertion when type is known:
   ```rust
   match ty {
       PiCode(_, Implicit, body) => insert_implicit_lambda(),
       _ => check_explicit()
   }
   ```
2. Test: `def id : {A : Type} → A → A = λ x. x`
3. Elaborate to: `λ {A} x. x`

### Phase 3: DOE (Week 3-4)

1. Add `PostponedCheck` struct
2. Add `postponed_checks: Vec<PostponedCheck>` to `SolverState`
3. Add `blocked_checks: HashMap<MetaId, Vec<usize>>`
4. Implement postponing when ty is meta-headed
5. Create placeholder metas
6. Hook into `solve_meta` to retry blocked checks
7. Implement end-of-file processing

### Phase 4: Testing (Week 5)

1. Test suite: [elaboration-zoo examples.txt](https://github.com/AndrasKovacs/elaboration-zoo/blob/master/06-first-class-poly/examples.txt)
2. Error messages for insertion ambiguity
3. Integration tests with existing elaborator

**Total:** ~5 weeks, ~150 LOC overhead for DOE

---

## Comparison with Alternatives

| Feature | DOE ⭐ | FCIF | Quick Look | Agda |
|---------|-------|------|------------|------|
| Complexity | Low | High | Medium | Medium |
| Core changes | None | Telescopes | None | None |
| Traversals | 1 pass | 1 pass | 2+ passes | 1 pass |
| Precision | High | Highest | Medium | Low |
| LOC overhead | ~150 | ~500+ | ~300 | N/A |

**Why DOE wins:**
- ✅ Simplest practical solution
- ✅ No core syntax changes (unlike FCIF)
- ✅ Single pass (unlike Quick Look)
- ✅ Stronger than Quick Look
- ✅ Production-proven (sixty language)

---

## References

**Primary source:** `wiki/research/implicit-arguments-first-class-polymorphism.md` (just created!)

**Key links:**
- [elaboration-zoo/06-first-class-poly](https://github.com/AndrasKovacs/elaboration-zoo/tree/master/06-first-class-poly)
- [FCIF Paper (ICFP 2020)](https://dl.acm.org/doi/10.1145/3408983)
- [GHC Quick Look Proposal](https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0274-quick-look-impredicativity.rst)

**Next steps:**
1. Review `wiki/research/implicit-arguments-first-class-polymorphism.md` for full details
2. Create ADR documenting decision to use DOE
3. Begin Phase 1 implementation

---

**Questions? Everything is documented in the wiki research page!**

