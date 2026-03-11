# MetaVariableId Migration Guide

## Overview

This guide helps you migrate code from the old `MetaVariableId(usize)` to the new composite `MetaVariableId { loc: Location, local_index: u16 }` structure.

## Breaking Changes

### 1. MetaVariableId Construction

**Old:**
```rust
let id = MetaVariableId(0);
let id = MetaVariableId(42);
```

**New:**
```rust
use hwml_core::common::Location;

let id = MetaVariableId::new(Location::UNKNOWN, 0);
let id = MetaVariableId::new(Location::UNKNOWN, 42);
```

### 2. MetaVariableId Pattern Matching

**Old:**
```rust
match meta_id {
    MetaVariableId(n) => println!("Meta {}", n),
}

fn foo(MetaVariableId(i): MetaVariableId) {
    // use i
}
```

**New:**
```rust
match meta_id {
    id => println!("Meta {}", id),  // Use Display impl
}

fn foo(id: MetaVariableId) {
    // Use id.loc and id.local_index if needed
}
```

### 3. Fresh Meta Allocation

**Old:**
```rust
let id = state.fresh_meta(ty);
```

**New:**
```rust
let id = state.fresh_meta(Location::UNKNOWN, ty);  // For now
// Future: let id = state.fresh_meta(current_location, ty);
```

### 4. Storage

**Old:**
```rust
struct SolverState {
    metas: Vec<MetaSlot>,
}

let slot = &state.metas[id.0];
```

**New:**
```rust
struct SolverState {
    metas: HashMap<MetaVariableId, MetaSlot>,
}

let slot = state.metas.get(&id).unwrap();
```

## New Features

### 1. Poisoned Metavariables

Create a poisoned metavariable for error recovery:

```rust
let error_meta = ctx.fresh_poisoned_meta(ty);
// This meta will unify with anything
```

Check if a meta is poisoned:

```rust
if ctx.state.borrow().is_poisoned(meta_id) {
    // Handle error case
}
```

### 2. Cycle Detection

Use `solve_checked` instead of `solve` to get cycle information:

```rust
match ctx.solve_checked(meta_id, solution) {
    Ok(()) => println!("Solved successfully"),
    Err(cycle) => println!("Cycle detected: {:?}", cycle),
}
```

### 3. Zonking

Replace solved metavariables with their solutions:

```rust
let zonked_term = ctx.zonk(&term);
// Solved metas are replaced, unsolved/poisoned are left as-is
```

## Migration Checklist

- [ ] Replace all `MetaVariableId(n)` with `MetaVariableId::new(Location::UNKNOWN, n)`
- [ ] Update pattern matches to not destructure MetaVariableId
- [ ] Update `fresh_meta` calls to include Location parameter
- [ ] Change Vec indexing to HashMap lookups
- [ ] Consider using `solve_checked` for better error reporting
- [ ] Add zonking pass at the end of elaboration

## Common Patterns

### Creating Test Metavariables

```rust
#[cfg(test)]
fn test_something() {
    let mut state = SolverState::new();
    let ty = Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0));
    let meta = state.fresh_meta(Location::UNKNOWN, ty);
    // ...
}
```

### Error Recovery in Elaboration

```rust
fn elaborate_expr(&self, expr: &SurfaceExpr) -> Result<Rc<Syntax>, Error> {
    match expr {
        SurfaceExpr::Undefined => {
            // Create a poisoned meta instead of failing
            let error_meta = self.ctx.fresh_poisoned_meta(expected_type);
            Ok(Syntax::metavariable_rc(expr.loc, error_meta, vec![]))
        }
        // ...
    }
}
```

### Checking for Cycles

```rust
fn solve_meta(&self, meta: MetaVariableId, solution: Rc<Syntax>) {
    match self.ctx.solve_checked(meta, solution.clone()) {
        Ok(()) => {
            println!("Solved {} successfully", meta);
        }
        Err(cycle) => {
            eprintln!("Cannot solve {}: cycle detected", meta);
            eprintln!("Cycle path: {:?}", cycle);
            // Create a poisoned meta instead
            let _ = self.ctx.fresh_poisoned_meta(self.ctx.meta_type(meta));
        }
    }
}
```

## Automated Migration

Most test code was migrated using sed:

```bash
# In hwml-core
cd crates/hwml-core/src
sed -i.bak 's/MetaVariableId(\([0-9]\+\))/MetaVariableId::new(Location::UNKNOWN, \1)/g' \
    syn/parse.rs syn/print.rs check.rs eval.rs equal.rs quote.rs pattern_unify.rs

# In hwml-elab
cd crates/hwml-elab/src
sed -i.bak 's/MetaVariableId(\([0-9]\+\))/MetaVariableId::new(Location::UNKNOWN, \1)/g' \
    engine.rs force.rs renaming.rs unify.rs
```

## FAQ

**Q: Why Location::UNKNOWN everywhere?**
A: For now, we use `Location::UNKNOWN` as a placeholder. Once we add location tracking to the elaboration context, we'll pass the actual source location.

**Q: What happens to unsolved metavariables?**
A: Unsolved non-poisoned metas are reported as errors by the typechecker. Poisoned metas are silently ignored (they represent errors that were already reported).

**Q: How do I debug metavariable issues?**
A: Use the `Display` impl for MetaVariableId, which shows both the location and local index. Enable debug logging to see solver activity.

**Q: Can I still use numeric IDs in tests?**
A: Yes! The parser supports `?[N]` syntax which maps to `MetaVariableId::new(Location::UNKNOWN, N)`.

