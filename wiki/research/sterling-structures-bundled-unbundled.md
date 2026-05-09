# Sterling's Approach to Structures: Bundled vs Unbundled, Refinements, and Field Dependencies

**Type:** Research Analysis  
**Created:** 2026-05-04  
**Confidence:** 0.95  
**Sources:** Jon Sterling's Pterodactyl worklog ([01HX], [01JQ]), Type theory literature  
**Relevance:** **CRITICAL** - Informs HWML's design for structures, coercions, and field dependencies

---

## Executive Summary

Jon Sterling's **Project Pterodactyl** takes a novel approach to structures in dependent type theory that addresses several long-standing issues:

1. **Large-by-default structures** - No universe level bureaucracy unless needed
2. **Theory refinements** - Structures with partial field instantiations  
3. **Bundled vs unbundled** - Explicit design choice with automatic coercions
4. **Selfification** - Avoid dependent coercions via singleton types
5. **Explicit casts** - User-controlled coercion (see [[disentangling-unification-coercion]])

**For HWML:** Sterling's approach offers a path to ergonomic hardware structures without universe headaches, plus a principled way to handle refinements (e.g., "a 32-bit signal" as refinement of "any signal").

---

## Part I: Large-by-Default Structures (Fuss-Free Universes)

### The Problem with Traditional Universe Hierarchies

**Traditional approach:** Every type must live in some universe `U_i`.

```lean
-- Traditional: Explicit universe levels everywhere
structure Category.{u,v} where
  ob : Type u
  hom : ob → ob → Type v
  -- operations...

-- Develops quickly into:
structure Functor.{u₁,v₁,u₂,v₂} (C : Category.{u₁,v₁}) (D : Category.{u₂,v₂}) where
  -- Even simple definitions get cluttered!
```

**Problems:**
- ❌ Universe variables proliferate (6+ per definition)
- ❌ Must predict size constraints upfront
- ❌ Implicit polymorphism doesn't remove complexity
- ❌ Debugging universe constraint graphs is painful

### Sterling's Solution: Work from the Top Down

**Key insight:** Don't constrain sizes unless you need to!

**Dream code (Pterodactyl):**
```
theory Category where
  ob : Type
  hom : ob → ob → Type
  -- operations and axioms...
```

**This is literally a large category** - no implicit polymorphism, no universe variables.

**Develop everything at top level:**
```
theory Functor where
  C : Category
  D : Category
  ob : C.ob → D.ob
  hom : (x y : C.ob) → C.hom x y → D.hom (ob x) (ob y)
  -- axioms...

theory NaturalTransformation where
  C : Category
  D : Category
  F : Functor / {C => C, D => D}  -- Refinement syntax!
  G : Functor / {C => C, D => D}
  go : (x : C.ob) → D.hom (F.ob x) (G.ob x)
  -- naturality...
```

**Specialize only when needed:**
```
theory LocallySmallCategory where
  V : Universe
  ob : Type
  hom : ob → ob → V  -- Now constrained to universe V
  
  inherit Category / {ob => ob, hom => hom}

theory SmallCategory where
  U : Universe
  ob : U  -- Even carrier is small
  inherit LocallySmallCategory / {V => U, ob => ob}
```

**Automatic implicit coercion:**
```
SmallCategory >-> LocallySmallCategory >-> Category
```

**Define category of small categories with no fuss:**
```
theory CategoryOfSmallStrictCategories where
  U : Universe
  
  scat : Category
  scat.ob => SmallStrictCategory / {U => U}
  scat.hom X Y => Functor / {C => X, D => Y}
  -- No universe headaches!
```

### Benefits for HWML

**Hardware structures are naturally large:**

```hwml
-- Top-level: No size constraints
structure Signal where
  width : Nat
  data : BitVec width
  valid : Bool

structure AXI4Stream where
  dataWidth : Nat
  tdata : BitVec dataWidth
  tvalid : Bool
  tready : Bool
  tlast : Bool
  tkeep : BitVec (dataWidth / 8)
  tstrb : BitVec (dataWidth / 8)
```

**Specialize when interfacing with synthesis:**

```hwml
-- Only constrain size when needed for actual hardware
structure SmallSignal where
  U : SynthesisUniverse  -- Types that can be synthesized
  width : U  -- Now width is "small" (synthesizable)
  data : BitVec width
  
  inherit Signal / {width => width, data => data}
```

---

## Part II: Theory Refinements

### What are Refinements?

**Refinement syntax:** `Theory / {field => value, ...}`

**Meaning:** A theory with some fields partially instantiated.

**Example:**
```
Monoid / {car => Nat}
```

**Telescope interpretation:**
```
-- Original Monoid telescope:
car : Type
join : car → car → car  
unit : car
join/assoc : (x y z : car) → join (join x y) z = join x (join y z)
join/unit/left : (x : car) → join unit x = x
join/unit/right : (x : car) → join x unit = x

-- After refinement {car => Nat}:
join : Nat → Nat → Nat
unit : Nat
join/assoc : (x y z : Nat) → join (join x y) z = join x (join y z)
join/unit/left : (x : Nat) → join unit x = x
join/unit/right : (x : Nat) → join x unit = x
```

**Remaining fields become the "constructor" for refined theory.**

### Constructor for Refined Theories

**Every theory expression `T` induces a constructor:**
```
make : <<T>> → T
```

Where `<<T>>` is the telescope of remaining (unrefined) fields.

**Example:**
```
make : (join : Nat → Nat → Nat) →
       (unit : Nat) →
       (join/assoc : ...) →
       (join/unit/left : ...) →
       (join/unit/right : ...) →
       Monoid / {car => Nat}
```

### Multiple Fields Example (Eckmann-Hilton Argument)

**Use case:** Two monoids sharing carrier, satisfying distributive law.

**Without refinements (clumsy):**
```
-- Have to manually unbundle
theory EckmannHilton where
  X : Type
  Mjoin : X → X → X
  Munit : X
  Massoc : ...
  Njoin : X → X → X
  Nunit : X
  Nassoc : ...
  dist : (u v w x : X) → Mjoin (Njoin u v) (Njoin w x) = Njoin (Mjoin u w) (Mjoin v x)
```

**With refinements (elegant):**
```
theory EckmannHilton where
  X : Type
  M : Monoid / {car => X}  -- Two monoids...
  N : Monoid / {car => X}  -- ...sharing carrier X
  dist : (u v w x : X) → M.join (N.join u v) (N.join w x) = N.join (M.mul u w) (M.mul v x)
```

**HWML application:**
```hwml
-- Multiple protocols on same data bus
structure DualProtocolBus where
  width : Nat

  axi : AXI4Stream / {dataWidth => width}
  ahb : AHBProtocol / {dataWidth => width}

  mux_select : Bool
  -- Constraint: Only one protocol active at a time
```

---

## Part III: Canonical Coercions for Refined Theories

### The Coercion Problem

**Question:** How do we coerce `T0/R0 → T1/R1`?

**Naive approach:** Apply constructor for `T1/R1`, project from `T0`.
- ❌ **Problem:** Eager η-expansion (term size blowup!)

### Sterling's Solution: Canonical Coercion via Diagrams

**Definition:** A canonical coercion `T0/R0 → T1/R1` arises from:

1. A canonical coercion `T0 → T1` (in the theory preorder)
2. Commuting squares ensure refinements compatible

**Diagram (concrete example):**
```
Monoid/R0      →    Semigroup/R1
    ↓                    ↓
  Monoid       →     Semigroup
```

Where:
- Top arrow is the **induced canonical coercion**
- Bottom arrow is the **forgetful coercion** (theory preorder)
- Left/right arrows are **refinement inclusions**
- **Squares commute** (definitionally!)

**Algorithm:**
1. Check that squares commute up to definitional equality
2. Define induced coercion as **syntactic constructor** (no actual η-expansion)
3. Associate correct **computation rules**

**Benefit:** Transparent from type theory POV, avoids term size blowup!

### Concrete Example

**Synthesize:**
```
X : Monoid / {car => Nat}
```

**Check at:**
```
Semigroup / {car => Nat}
```

**Canonical coercion exists:**
```
Monoid/       → Semigroup/
{car=>Nat}      {car=>Nat}
    ↓                ↓
  Monoid      →  Semigroup
```

**Elaborates to** (conceptually, not explicitly written):
```
coerce X = make {
  car := Nat,                  -- Already refined
  join := X.join,              -- Project from Monoid
  assoc := X.join/assoc        -- Project proof
}
```

But represented as **primitive coercion** to avoid expansion!

---

## Part IV: Selfification - Avoiding Dependent Coercions

### The Dependent Coercion Problem

**Problematic scenario:**
```
cool (X : Monoid) : Semigroup / {car => X.car}
cool X => X
```

**Question:** How to justify returning `X`?

**Challenge:** Type we're checking against **depends on X.car**, seemingly requiring:
```
Monoid → (X : Monoid) → Semigroup / {car => X.car}
```

This is a **dependent coercion** - notoriously problematic!

**Luo & Soloviev's issues:**
- Most expressive rules break transitivity
- Compositional dependent coercions don't work

**Lean's approach:**
- Has dependent coercions
- **Explicitly doesn't support chaining** (likely due to these issues)

### Sterling's Selfification Trick

**Key insight (from ML Modules):** Transform dependent coercion into non-dependent one!

**Algorithm:**
1. We have `X : Monoid`, need `Semigroup / {car => X.car}`
2. **Don't search for** `Monoid → Semigroup / {car => X.car}` (dependent!)
3. **Instead:** Construct maximal refinement of `Monoid` that contains only `X`:

```
Monoid / {
  car => X.car,
  join => X.join,
  unit => X.unit,
  assoc => X.assoc,
  join/unit/left => X.join/unit/left,
  join/unit/right => X.join/unit/right
}
```

4. This is a **definitional singleton type** containing only `X`
5. **Now search for** coercion from this singleton to `Semigroup / {car => X.car}`
6. This coercion **exists** and is **non-dependent**!

**Elaboration state:**
```
Mode shift: X : Monoid → Semigroup / {car => X.car}

Step 1 (Selfify):
  Refine Monoid to Monoid/{car => X.car, join => X.join, ...}
  (This is definitional singleton containing only X)

Step 2 (Find coercion):
  Search: Monoid/{...all X's fields...} → Semigroup/{car => X.car}
  Result: Exists! (forgetful + refinement)

Step 3 (Apply):
  Insert coercion, continue
```

**Result:** No actual dependent coercions in the type system!

### Heritage: ML Modules Selfification

**Source:** Harper & Lillibridge's "VALUE" rules, Leroy's signature strengthening

**ML Modules example:**
```sml
signature MONOID = sig
  type t
  val unit : t
  val op : t -> t -> t
end

functor F (M : MONOID) : sig  (* dependent signature *)
  type t = M.t
  (* ... *)
end = struct
  (* Selfification allows this! *)
end
```

**Key papers:**
- Harper & Lillibridge (1994) - Translucent sums and singleton kinds
- Leroy (1994) - Manifest types, modules, separate compilation
- Stone & Harper (2006) - Deciding type equivalence with singleton kinds
- Crary (2003) - Singleton types

---

## Part V: Bundled vs Unbundled Structures

### The Choice

**Bundled:** All data packaged together in a record.
```
structure BundledMonoid where
  carrier : Type
  op : carrier → carrier → carrier
  unit : carrier
  assoc : ...
```

**Unbundled:** Carrier separate, operations parameterized.
```
class Monoid (α : Type) where
  op : α → α → α
  unit : α
  assoc : ...
```

### Sterling's Approach: Bundled with Refinements

**Pterodactyl uses bundled by default:**
```
theory Monoid where
  car : Type
  join : car → car → car
  unit : car
  -- axioms...
```

**Unbundled effect via refinement:**
```
Monoid / {car => Nat}  -- "Monoid structure on Nat"
```

**Automatic coercion between them:**

**Bundled → Unbundled:**
```
M : Monoid
-- Can automatically treat as:
M.car : Type
MonoidOnM : Monoid / {car => M.car}
```

**Unbundled → Bundled:**
```
ops : Monoid / {car => Nat}
-- Can construct bundled version:
BundledMonoidNat : Monoid
BundledMonoidNat.car := Nat
BundledMonoidNat.join := ops.join
...
```

### Advantages for HWML

**Hardware naturally suggests both:**

**Bundled (interface specification):**
```hwml
structure AXI4Stream where
  dataWidth : Nat
  tdata : BitVec dataWidth
  tvalid : Bool
  tready : Bool
  -- Complete interface specification
```

**Unbundled (operations on existing type):**
```hwml
class HasValid (α : Type) where
  valid : α → Bool

-- Can view AXI4Stream as HasValid:
instance : HasValid (AXI4Stream w) where
  valid := AXI4Stream.tvalid
```

**Refinement connects them:**
```hwml
axi : AXI4Stream 32

-- Treat as "thing with valid signal":
axi_has_valid : HasValid / {α => AXI4Stream 32}
axi_has_valid = axi  -- Automatic coercion!
```

---

## Part VI: Field Dependencies - Forward and Backward?

### Standard (Forward) Dependencies

**What we have:** Later fields depend on earlier ones.

```hwml
structure Vector where
  length : Nat
  data : Array length  -- ✅ Depends on earlier field
```

**Telescope:**
```
(length : Nat, data : Array length)
```

**This is standard Σ-type behavior.**

### Backward Dependencies?

**Question:** Can a field's type depend on a **future** field?

```hwml
structure BackwardDep where
  data : Array length  -- ❓ Depends on later field?
  length : Nat
```

**Answer:** **No, not directly** in standard dependent type theory!

**Why not:**
1. **Σ-types are sequential:** `Σ x:A. B(x)` requires `B` to depend only on `x`
2. **Elaboration order:** Must know type of `data` before encountering `length`
3. **Decidable type checking:** Need to compute types left-to-right

### Simulating Backward Dependencies

**Option 1: Reorder Fields**
```hwml
-- Just put length first!
structure Vector where
  length : Nat
  data : Array length  -- Now forward dependency
```

**Option 2: Use Parameters**
```hwml
structure Vector (length : Nat) where
  data : Array length
  -- length is parameter, not field
```

**Option 3: Existential (hide dependency)**
```hwml
structure SomeVector where
  data : Σ (n : Nat). Array n  -- Package length with data

  -- Can project:
  length : Nat
  length := data.fst
```

**Option 4: Mutual Definition**
```hwml
-- Not directly supported in standard DT, but hypothetically:
mutual
  structure ForwardRef where
    data_ref : DataType length_ref
    length_ref : Nat
```

**But this is problematic** - breaks decidable type checking!

### The Core Issue: Decidability

**Type checking algorithm needs:**
1. Check `data : Array length` requires knowing `length : Nat`
2. But `length` hasn't been elaborated yet!
3. **Circular dependency in elaboration**

**Even with mutual blocks:**
- How to infer types before knowing all fields?
- Unification becomes undecidable
- Termination checking fails

**Contrast with mutual data types:**
```lean
mutual
  inductive Tree where
    | leaf : Nat → Tree
    | node : Forest → Tree

  inductive Forest where
    | nil : Forest
    | cons : Tree → Forest → Forest
end
```

**This works because:**
- Type names are declared upfront
- Constructors reference already-declared types
- No circular dependency in *type formation*, only in *type usage*

**Records are different:**
- Field types computed during elaboration
- Dependencies create type formation circularity
- Not reducible to mutual inductives

---

## Part VII: What Would Backward Dependencies Require?

### Theoretical Changes Needed

**1. Unordered Telescopes**

**Current:** Sequential telescope `(x₁:A₁, x₂:A₂(x₁), ..., xₙ:Aₙ(x₁,...,xₙ₋₁))`

**Needed:** Dependency graph where fields can reference each other (acyclic!)

```
Structure with dependency graph:
  length : Nat
  width : Nat
  data : Array (length * width)  -- Depends on both length and width
  metadata : Meta data            -- Depends on data (earlier)

Dependency graph:
  length ──┐
           ├──> data ──> metadata
  width ───┘
```

**Elaboration:** Topological sort of dependency graph.

### 2. Bidirectional Elaboration Extensions

**Current:** Elaborate fields left-to-right, accumulating context.

**Needed:**
1. **First pass:** Collect all field names
2. **Second pass:** Resolve dependencies (topological order)
3. **Third pass:** Type check in dependency order

**Challenge:** User writes in one order, elaborates in another!

### 3. Type-Level Constraint Solving

**Example:**
```hwml
structure Constrained where
  sum : Nat
  a : Nat
  b : Nat
  constraint : a + b = sum  -- Constraint relates fields
```

**This requires:**
- Bidirectional constraint propagation
- Unification of type-level equations
- SMT-like solving at type level

**Quickly becomes undecidable!**

### 4. Implementation Challenges

**Rust-like challenges:**
```rust
struct Vector {
    length: usize,
    data: [u8; length],  // ❌ Doesn't work in Rust!
}
```

**Rust uses `const generics` instead:**
```rust
struct Vector<const N: usize> {
    data: [u8; N],
}
```

**For dependent types:**
- Could elaborate `structure Vector where ...` into parameter form
- User writes unordered, elaborates to ordered
- Complex bidirectional mapping for error messages

---

## Part VIII: Proposal for HWML

### Conservative Approach (Recommended)

**Stick with forward dependencies:**
```hwml
structure Signal where
  width : Nat
  data : BitVec width  -- ✅ Forward dependency
  valid : Bool
```

**Use parameters for "shared" dependencies:**
```hwml
structure Matrix (rows cols : Nat) where
  data : Array (rows * cols)
  -- rows, cols are parameters, not fields
```

**Rationale:**
- ✅ Decidable type checking
- ✅ Predictable elaboration
- ✅ Matches Lean 4/Agda/Coq
- ✅ Simpler implementation

### Experimental Approach (Future Research)

**Could explore limited backward dependencies:**

**Restriction:** Backward dependency only on fields **without dependencies themselves**.

**Example (allowed):**
```hwml
structure LimitedBackward where
  data : Array width    -- Depends on width
  width : Nat           -- No dependencies

  -- Elaborates to:
  -- width : Nat, data : Array width
```

**Example (disallowed):**
```hwml
structure TooComplex where
  data : Array (width * height)  -- Depends on width, height
  width : Nat                    -- No deps
  height : Nat                   -- No deps
  metadata : Meta data           -- Depends on data

  -- ❌ Circular: metadata depends on data depends on width/height
```

**Algorithm:**
1. Build dependency graph
2. Check acyclic
3. Topological sort
4. Elaborate in dependency order
5. **Map user order ↔ elaboration order** (for error messages)

**Benefits:**
- More flexible field ordering
- Hardware specs often list outputs before inputs

**Costs:**
- More complex elaboration
- Error messages harder (must map back to user order)
- Potential performance hit

### Pragmatic Middle Ground

**Allow reordering in simple cases:**

**User writes:**
```hwml
structure AXI4Stream where
  -- Outputs first (natural for hardware specs)
  tdata : BitVec dataWidth
  tvalid : Bool

  -- Config at end (also natural)
  dataWidth : Nat
```

**Elaborator:**
1. Detect `tdata` depends on `dataWidth`
2. **Automatically reorder** to: `(dataWidth : Nat, tdata : BitVec dataWidth, tvalid : Bool)`
3. **Remember user order** for pretty-printing

**Error messages use user order:**
```
Error in field 'tdata': ...
  (note: tdata is defined before dataWidth in source,
   but elaborated after due to dependency)
```

**This gives:**
- ✅ User flexibility
- ✅ Decidable checking
- ✅ Clear elaboration rules
- ⚠️ Moderate implementation complexity

---

## Part IX: Sterling's Unified Treatment

### Theory Preorder + Refinements + Coercions

**Sterling's design unifies:**

1. **Theory hierarchy** (Magma < Semigroup < Monoid < Group)
2. **Refinements** (Monoid/{car => Nat})
3. **Canonical coercions** (lifting across refinements)
4. **Explicit casts** (user-controlled via `cast`)

**All fit together coherently!**

**Example flow:**
```
Define: theory Monoid
Refine: Monoid / {car => Nat}
Specialize: LocallySmallMonoid / {V => U₀, car => Nat}
Coerce: SmallMonoid → Monoid (via canonical coercion)
Cast: X : SmallMonoid, need Monoid → cast X
```

### For HWML

**Hardware hierarchy:**
```hwml
-- Base
structure Signal where
  width : Nat
  data : BitVec width

-- Clocked (refine + extend)
structure ClockedSignal where
  clk : ClockDomain
  sig : Signal

-- Specific width (refinement)
Signal / {width => 8}  -- "8-bit signal"

-- Specific clock (refinement)
ClockedSignal / {clk => SystemClock}

-- Both (multiple refinements)
ClockedSignal / {clk => SystemClock, sig => Signal/{width => 8}}
```

**Automatic coercions:**
```hwml
sig8 : Signal / {width => 8}

-- Can use where Signal expected:
fn (s : Signal) : Bool

fn sig8  -- ✅ Automatic coercion via refinement inclusion
```

**Explicit casts when ambiguous:**
```hwml
sig : Signal

-- Need specific width:
sig8 : Signal / {width => 8}
sig8 = cast sig  -- ❌ Error: Can't infer width

-- Must provide:
sig8 = cast_with {width => 8} sig  -- ✅ Explicit
```

---

## References

### Primary Sources

**Jon Sterling's Pterodactyl Worklog:**
- [01HX] "Fuss-free universe hierarchies" (October 6, 2025)
- [01JQ] "Disentangling unification and implicit coercion" (January 27, 2026)
- [01HN] "Lifting coercions to theory refinements" (October 1, 2025)
- Full worklog: [jonmsterling.com/01HC](https://www.jonmsterling.com/01HC/)

### ML Modules Selfification

**Historical sources:**
- Harper & Lillibridge (1994) "A type-theoretic approach to higher-order modules with sharing"
- Leroy (1994) "Manifest types, modules, and separate compilation"
- Stone & Harper (2006) "Deciding type equivalence with a unification oracle"
- Crary (2003) "Toward a foundational typed assembly language"

### Dependent Coercions

**Problematic approaches:**
- Luo (1999) "Coercive subtyping"
- Luo & Soloviev (2000) "Dependent coercions"
- Lean 4 documentation on dependent coercions (no chaining support)

### Universe Hierarchies

**Referenced work:**
- Bezem, Coquand, Dybjer, Escardó (2023) "Type Theory with Explicit Universe Polymorphism"
- McBride (2012) "Crude but Effective Stratification"
- Allais, McBride, Boutillier (2013) "New equations for neutral terms"

### HWML Wiki Cross-References

- [[disentangling-unification-coercion]] - Sterling's explicit cast proposal (deep dive)
- [[structure-types-theory-implementation]] - Type theory foundations
- [[type-unification-structures-implementation]] - Unification with records
- [[research/crude-but-effective-stratification]] - McBride's universe approach

---

## Conclusion

Sterling's approach to structures offers **several key innovations**:

### 1. Large-by-Default Eliminates Universe Bureaucracy

**Traditional:**
```lean
structure Category.{u,v,w,x,y,z}  -- Universe parameter explosion
```

**Sterling:**
```
theory Category  -- No universe constraints unless needed
```

**For HWML:** Hardware structures don't need universe constraints until synthesis!

### 2. Refinements Provide Flexible Partial Instantiation

**Enables:**
- Sharing carriers between structures (Eckmann-Hilton)
- Gradual specialization (Category → LocallySmallCategory → SmallCategory)
- Hardware: `Signal/{width => 8}` for "8-bit signal"

### 3. Selfification Avoids Dependent Coercion Issues

**Transform dependent coercion into non-dependent:**
- Maximal singleton refinement
- Non-dependent canonical coercion
- No Luo & Soloviev problems!

### 4. Bundled + Refinements = Best of Both Worlds

**Bundled by default:**
```
theory Monoid  -- All data together
```

**Unbundled effect via refinement:**
```
Monoid / {car => Nat}  -- "Monoid on Nat"
```

### 5. Explicit Casts for Reliability

**User controls unification vs coercion interaction:**
```
cast X  -- Explicit, predictable
```

See [[disentangling-unification-coercion]] for full motivation.

### Backward Dependencies: Recommendation for HWML

**Conservative (Phase 1):** Forward dependencies only
- ✅ Decidable
- ✅ Predictable
- ✅ Matches existing systems

**Pragmatic (Phase 2):** Automatic reordering
- Allow user to write in any order
- Elaborate in dependency order
- Remember mapping for errors

**Experimental (Phase 3+):** True backward dependencies
- Dependency graph elaboration
- Bidirectional constraint solving
- Research project, not production yet!

**Bottom line:** Backward dependencies are **theoretically possible** with significant elaborator changes, but **not practically necessary** - reordering + parameters solve most use cases.

---

**Last Updated:** 2026-05-04
**Status:** ✅ Comprehensive analysis complete
**Confidence:** 0.95 (Sterling's published work + type theory foundations)

**Cross-References:**
- [[disentangling-unification-coercion]]
- [[structure-types-theory-implementation]]
- [[type-unification-structures-implementation]]
- [[research/crude-but-effective-stratification]]
