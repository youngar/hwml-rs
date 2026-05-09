# ADR-012: Inductive Type Namespace Scoping

**Status:** Approved ✅  
**Date:** 2026-05-05  
**Deciders:** Core team  
**Related:** [[ADR-011-module-resolution-file-discovery]], [[ADR-007-salsa-driven-compilation]]

---

## Context

When elaborating inductive type declarations, we must determine the **namespace context** in which parameters, indices, universe levels, and constructors are elaborated.

For example, given:
```hwml
inductive Std.Vec (A : Type) : (n : Nat) -> Type where
    | vnil : Vec A zero
    | vcons : (n : Nat) -> A -> Vec A n -> Vec A (succ n)
```

The question is: **What namespace scope should `Nat`, `zero`, and `succ` resolve from?**

### The Problem

We encountered a critical bug where inductive type elaboration was **inconsistent**:

1. **Constructors** were elaborated in the inductive's namespace (`Std.Vec`)
2. **Parameters and indices** were elaborated in the outer/parent namespace

This caused name resolution failures:

```
[RESOLVE] Looking up path: Nat
[HOIST] Phase 1 failed for Std/Vec: NotInScope { name: "Nat", span: None }
```

When elaborating the index `(n : Nat)`:
- Resolver was in the parent namespace context (or root)
- `Nat` could not resolve because it's defined as `Std.Nat`
- The lookup failed because we weren't in the `Std` namespace

However, constructors worked fine because they were already being elaborated with the inductive's namespace pushed!

### Comparison with Lean

Lean uses a different scoping model:
- Inductive parameters/indices are elaborated in the **parent** namespace
- Constructors are elaborated in the **inductive's** namespace
- This allows precise control but creates complexity

---

## Decision

**All parts of an inductive type declaration (parameters, indices, universe, constructors) are elaborated in the inductive type's own namespace.**

For `inductive Std.Vec (A : Type) : (n : Nat) -> Type`:

1. Push namespace `Std.Vec` (the inductive's full path)
2. Elaborate parameters in `Std.Vec` namespace
3. Elaborate indices in `Std.Vec` namespace  
4. Elaborate universe in `Std.Vec` namespace
5. Elaborate constructors in `Std.Vec` namespace

When resolving bare names like `Nat`:
- Start in current namespace: `Std.Vec`
- Walk up to parent: `Std`
- Find `Std.Nat` in the stub table ✅

### Rationale

**Consistency:** All parts of the inductive see the same namespace context. No special cases.

**Simplicity:** One rule to remember - "everything in an inductive is scoped to the inductive's namespace"

**Predictability:** Name resolution behaves the same way everywhere in the inductive definition

**Works with qualified names:** The inductive's qualified name already encodes the logical structure (`Std.Vec` is in the `Std` namespace family)

### Divergence from Lean

This differs from Lean's scoping model where parameters/indices use the parent namespace. We chose this approach because:

1. **HWML's namespace model is simpler** - We don't have Lean's complex section/variable mechanism
2. **Consistency is more important** - Hardware engineers prefer uniform rules
3. **It just works** - Name resolution naturally walks up the namespace hierarchy

---

## Implementation

### Core Changes

**1. `elab_inductive_impl` in `crates/hwml-elab/src/elab/decl.rs`:**

```rust
fn elab_inductive_impl<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    ind: &Inductive,
    lenient: bool,
) -> Result<ElaboratedInductive<'db>, ElabError<'db>>
where
    Db: salsa::Database,
{
    let name = ind.name.value.to_vec();

    // CRITICAL: Push the inductive type's namespace for ALL elaboration
    let ind_path = crate::util::surface_id_to_path(db, &ind.name)
        .ok_or(ElabError::NotInScope { ... })?;
    
    // Push namespace scope for the inductive type
    let ind_resolver = elab.kernel.resolver.push_namespace(db, &ind_path);

    // Elaborate parameters in the inductive's namespace
    let (params, param_ctx) = {
        let mut inner = Elaborator {
            kernel: crate::kernel::Kernel::new(
                elab.kernel.global,
                elab.kernel.ctx.clone(),
                elab.kernel.state,
                &ind_resolver,  // ← Use namespace-pushed resolver
                elab.kernel.stub_table,
            ),
        };
        elab_telescope(db, &mut inner, &ind.parameters.groups)?
    };

    // Elaborate indices (still in inductive's namespace)
    let (indices, _idx_ctx) = {
        let mut inner = Elaborator {
            kernel: crate::kernel::Kernel::new(
                elab.kernel.global,
                param_ctx.clone(),
                elab.kernel.state,
                &ind_resolver,  // ← Same resolver
                elab.kernel.stub_table,
            ),
        };
        elab_telescope(db, &mut inner, &ind.indices.groups)?
    };

    // Elaborate universe (still in inductive's namespace)
    // Elaborate constructors (still in inductive's namespace)
    // ...
}
```

**2. Phase 1 hoisting in `crates/hwml-elab/src/program.rs`:**

```rust
fn elab_inductive_statement<'db, Db>(
    // ...
) {
    let ind_path = surface_id_to_path(db, &ind.name)?;
    let qname = resolver.qualify_path(db, &ind_path);

    // Push the inductive's namespace for parameter/index elaboration
    let ind_resolver = resolver.push_namespace(db, &ind_path);

    // PHASE 1: Elaborate header with namespace-pushed resolver
    let mut elab = Elaborator::new(
        global,
        ElabCtx::empty(),
        &mut header_state,
        &ind_resolver,  // ← Use namespace-pushed resolver
        stub_table,
    );
    // ...
}
```

**3. SCC-based elaboration in `crates/hwml-elab/src/scc_elab.rs`:**

Same pattern - push the inductive's namespace before elaborating headers in Phase 1.

---

## Consequences

### Positive

1. **Consistent scoping:** All parts of an inductive definition see the same namespace context
2. **Bug fix:** Resolves the hoisting failure for `Nat` in `Vec.hwml`
3. **Predictable:** One simple rule - "everything in an inductive is in that inductive's namespace"
4. **Natural name resolution:** Walking up namespace hierarchy (`Std.Vec` → `Std`) works intuitively
5. **Easier to teach:** No special cases to explain to users

### Negative

1. **Diverges from Lean:** Lean users may find this unfamiliar
   - *Mitigation:* Document the difference clearly. HWML's simpler namespace model justifies the divergence.

2. **Slightly less precise control:** Can't have parameters in parent scope and constructors in child scope
   - *Mitigation:* Not needed in practice. Users can always use fully qualified names if desired.

### Neutral

- **Different mental model:** Hardware engineers coming from Verilog won't have preconceptions, so this is fine
- **Namespace walking:** Relies on resolver walking up namespace hierarchy, which already works

---

## Alternatives Considered

### Alternative 1: Lean-style Split Scoping

**What:** Elaborate parameters/indices in parent namespace, constructors in inductive's namespace.

**Why rejected:**
- Adds complexity with no clear benefit
- The bug we encountered shows this creates inconsistency
- HWML doesn't have Lean's section/variable mechanism to support this model

### Alternative 2: Always Use Parent Namespace

**What:** Elaborate everything (params, indices, constructors) in the parent namespace.

**Why rejected:**
- Constructors would not be scoped under the inductive type name
- For `inductive Std.Vec`, constructors should be `Std.Vec.vnil`, not `Std.vnil`
- Breaks the logical nesting structure

### Alternative 3: Require Fully Qualified Names

**What:** Force users to write `Std.Nat` instead of allowing `Nat` to resolve.

**Why rejected:**
- Verbose and repetitive
- Defeats the purpose of namespaces
- Users expect name resolution to work hierarchically

---

## Success Metrics

### Correctness
- [x] `Vec.hwml` elaborates successfully (no `Nat` lookup failure)
- [x] Parameters can reference types from parent namespaces
- [x] Indices can reference types from parent namespaces
- [x] Constructors are properly qualified under the inductive name
- [x] Name resolution walks up namespace hierarchy correctly

### Consistency
- [x] All three elaboration paths use the same resolver:
  - `elab_inductive_impl` (normal elaboration)
  - `elab_inductive_statement` (Phase 1 hoisting)
  - `elaborate_headers` (SCC-based elaboration)

---

## References

**Related Code:**
- `crates/hwml-elab/src/elab/decl.rs` - Core inductive elaboration
- `crates/hwml-elab/src/program.rs` - Phase 1 hoisting
- `crates/hwml-elab/src/scc_elab.rs` - SCC-based elaboration

**Related ADRs:**
- [[ADR-011-module-resolution-file-discovery]] - Library-level aggregation and namespace model
- [[ADR-007-salsa-driven-compilation]] - Demand-driven queries

**Lean's Approach:**
- Lean 4 uses parent namespace for parameters: https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html

---

**Status:** Approved ✅
**Date:** 2026-05-05

**Next Steps:**
1. [x] Update `elab_inductive_impl` to push namespace before parameter elaboration
2. [x] Update `elab_inductive_statement` to push namespace in Phase 1
3. [x] Update `elaborate_headers` to push namespace in SCC elaboration
4. [x] Verify `Vec.hwml` and other stdlib files elaborate successfully
5. [ ] Add tests for cross-namespace type references in inductive definitions
6. [ ] Document this behavior in user-facing language guide

