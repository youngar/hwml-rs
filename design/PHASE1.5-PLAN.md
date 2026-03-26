# Phase 1.5: Inductive Types & Pattern Matching

## Goal

Add pattern matching and inductive datatypes to the NbE core engine while maintaining the proven correctness of Phase 1.

## Architecture Overview

### The Key Insight

Constructors are **rigid** - they don't compute, they just collect arguments.
Case expressions have **duality**:
- If scrutinee is a known constructor → **reduce** (select branch)
- If scrutinee is neutral (variable/meta) → **get stuck** (add to spine)

### Data Structures

#### 1. Syntax Extensions

```rust
pub enum Syntax<'db> {
    // ... existing variants (UniverseCode, PiCode, Lam, App, etc.)
    
    // NEW: Inductive types
    TypeCon(DefId, Vec<RcSyntax<'db>>),  // Type constructor + args
    DataCon(DefId, Vec<RcSyntax<'db>>),  // Data constructor + args
    Case {
        scrutinee: RcSyntax<'db>,
        motive: Binder<RcSyntax<'db>>,   // Return type function
        branches: Vec<Branch<'db>>,
    },
}

pub struct Branch<'db> {
    pub ctor_id: DefId,
    pub arity: usize,           // Number of constructor arguments
    pub body: RcSyntax<'db>,    // Body with arity binders
}
```

#### 2. Value Extensions

```rust
pub enum Value<'db> {
    // ... existing variants
    
    // NEW: Evaluated constructors
    TypeCon(DefId, Vec<RcValue<'db>>),
    DataCon(DefId, Vec<RcValue<'db>>),
    
    // Neutral stays the same, but spine changes
    Neutral(RcNeutral<'db>),
}
```

#### 3. Spine Upgrade: Eliminators

**CRITICAL CHANGE:** Spine is no longer `Vec<RcValue>`, it's `Vec<Elim>`!

```rust
pub struct Neutral<'db> {
    pub head: Head,
    pub spine: Vec<Elim<'db>>,  // ← Changed from Vec<RcValue>
}

pub enum Elim<'db> {
    /// Function application
    App(RcValue<'db>),
    
    /// Stuck case expression
    /// Contains the motive and branches, waiting for head to become concrete
    Case {
        motive: Closure<'db>,
        branches: Vec<Branch<'db>>,
    },
}
```

### Evaluation Logic

#### Constructor Application

Constructors accumulate arguments (like currying):

```rust
// eval(TypeCon(Vec), A) → TypeCon(Vec, [A])
// eval(App(TypeCon(Vec, [A]), n)) → TypeCon(Vec, [A, n])
```

#### Case Evaluation (The Duality)

```rust
match scrutinee_value {
    // SCENARIO 1: Known constructor → REDUCE
    Value::DataCon(ctor_id, ctor_args) => {
        // Find matching branch
        let branch = find_branch(ctor_id);
        
        // Extend environment with constructor arguments
        let mut branch_env = env.clone();
        for arg in ctor_args {
            branch_env.push(arg);
        }
        
        // Evaluate branch body
        eval(global, &branch_env, &branch.body)
    }
    
    // SCENARIO 2: Neutral → GET STUCK
    Value::Neutral(neu) => {
        // Add Case eliminator to spine
        let mut new_spine = neu.spine.clone();
        new_spine.push(Elim::Case { motive, branches });
        
        Value::Neutral(Neutral {
            head: neu.head,
            spine: new_spine,
        })
    }
}
```

### Quotation Logic

#### Quoting Constructors

```rust
Value::TypeCon(id, args) => {
    let quoted_args = args.iter()
        .map(|arg| quote(global, depth, arg))
        .collect();
    Syntax::TypeCon(id, quoted_args)
}

Value::DataCon(id, args) => {
    let quoted_args = args.iter()
        .map(|arg| quote(global, depth, arg))
        .collect();
    Syntax::DataCon(id, quoted_args)
}
```

#### Quoting Neutrals with Case Eliminators

```rust
fn quote_neutral(global, depth, neutral) -> Syntax {
    let mut result = quote_head(neutral.head, depth);
    
    for elim in &neutral.spine {
        match elim {
            Elim::App(arg) => {
                let arg_syn = quote(global, depth, arg);
                result = Syntax::App(result, arg_syn);
            }
            
            Elim::Case { motive, branches } => {
                // Quote the motive closure
                let fresh_var = Value::var(Level::new(depth));
                let motive_body = motive.apply(global, fresh_var)?;
                let motive_syn = quote(global, depth + 1, &motive_body)?;
                
                // Quote each branch
                let branches_syn = branches.iter()
                    .map(|b| quote_branch(global, depth, b))
                    .collect();
                
                result = Syntax::Case {
                    scrutinee: result,
                    motive: Binder::anonymous(motive_syn),
                    branches: branches_syn,
                };
            }
        }
    }
    
    result
}
```

## Implementation Steps

### Step 1: Update Data Structures (30 min)
- [ ] Add `TypeCon`, `DataCon`, `Case` to `Syntax`
- [ ] Add `TypeCon`, `DataCon` to `Value`
- [ ] Create `Elim` enum
- [ ] Update `Neutral` to use `Vec<Elim>`
- [ ] Add `Branch` struct

### Step 2: Update Evaluation (1 hour)
- [ ] Handle `TypeCon` evaluation
- [ ] Handle `DataCon` evaluation
- [ ] Handle constructor application (accumulate args)
- [ ] Handle `Case` evaluation (reduce or get stuck)
- [ ] Update neutral application to use `Elim::App`

### Step 3: Update Quotation (1 hour)
- [ ] Quote `TypeCon` values
- [ ] Quote `DataCon` values
- [ ] Quote neutrals with `Elim::App`
- [ ] Quote neutrals with `Elim::Case`

### Step 4: GlobalEnv Extensions (30 min)
- [ ] Add constructor info storage
- [ ] Add lookup methods for type/data constructors

### Step 5: Write Tests (2 hours)
- [ ] Test Nat type (Zero, Succ constructors)
- [ ] Test Bool type (True, False constructors)
- [ ] Test case on known constructor (reduces)
- [ ] Test case on variable (gets stuck)
- [ ] Test identity law with case expressions
- [ ] Test nested case expressions

## Test Cases

### Test 1: Nat Constructors
```rust
// Zero : Nat
// Succ : Nat → Nat
let zero = DataCon(Zero, []);
let one = App(DataCon(Succ), DataCon(Zero));
assert_nbe_identity(zero);
assert_nbe_identity(one);
```

### Test 2: Case Reduction
```rust
// match Zero { Zero => True | Succ n => False }
// Should reduce to True
let case_expr = Case {
    scrutinee: DataCon(Zero),
    branches: [
        Branch { ctor: Zero, body: DataCon(True) },
        Branch { ctor: Succ, body: DataCon(False) },
    ],
};
assert_eq!(eval(case_expr), DataCon(True));
```

### Test 3: Stuck Case
```rust
// λn. match n { Zero => True | Succ m => False }
// Should quote back to itself (identity law)
let stuck_case = Lam(Case {
    scrutinee: Var(0),  // Bound variable
    branches: [...],
});
assert_nbe_identity(stuck_case);
```

## Success Criteria

- [ ] All Phase 1 tests still pass
- [ ] 5+ new tests for inductive types pass
- [ ] Identity law holds for case expressions
- [ ] Can represent Nat, Bool, List types
- [ ] Stuck cases quote correctly

## Estimated Effort

- Data structures: 30 min
- Evaluation: 1 hour
- Quotation: 1 hour
- GlobalEnv: 30 min
- Tests: 2 hours
- **Total: ~5 hours**

## Next Phase Dependencies

Phase 2 (Unification) will need:
- Constructor unification (structural equality)
- Case expression unification (branch-by-branch)
- Spine unification with eliminators

Phase 3 (Elaboration) will need:
- Exhaustiveness checking
- Constructor type checking
- Motive inference


