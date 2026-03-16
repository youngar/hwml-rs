# Poisoned Metavariables and Location-Derived IDs

## Overview

This document describes the implementation of the **Poisoned Metavariable** error recovery strategy and **Location-Derived MetaVariableId** architecture in the HWML elaborator.

## Motivation

### Problem 1: Error Cascades
When elaboration encounters an error (e.g., type mismatch, undefined variable), we need a way to continue elaborating the rest of the program without generating hundreds of spurious errors. Traditional approaches add an explicit `Error` node to the AST, but this pollutes the mathematically pure Core IR.

### Problem 2: Salsa Determinism
Salsa's incremental computation requires that all queries be deterministic. Using a global atomic counter for metavariable IDs breaks this guarantee because thread scheduling can affect the order of ID allocation, causing cache invalidation.

## Solution: Poisoned Metavariables

Instead of adding `SyntaxData::Error` to the Core IR, we use **poisoned metavariables**:

1. When elaboration encounters an error, create a fresh metavariable with the `poisoned` flag set
2. The unifier short-circuits when it encounters a poisoned metavariable: `unify(Poisoned, _) = Ok(())`
3. Poisoned metavariables are never solved and are left as-is during zonking
4. The typechecker can report unsolved non-poisoned metas as errors, while poisoned metas are silently ignored

### Benefits
- **Core IR remains pure**: No `Error` variant needed
- **Prevents cascades**: Poisoned metas unify with anything
- **Out-of-band diagnostics**: Errors stored separately in `SolverState`
- **Graceful degradation**: Elaboration continues after errors

## Solution: Location-Derived IDs

Instead of using a global counter, `MetaVariableId` is now a composite struct:

```rust
pub struct MetaVariableId {
    pub loc: Location,        // Salsa-interned location
    pub local_index: u16,     // Local counter at this location
}
```

### ID Generation
- Each `Location` has its own counter stored in `SolverState::local_counters`
- When creating a fresh meta at location `L`, increment `local_counters[L]`
- The ID is `{ loc: L, local_index: counter }`

### Benefits
- **Deterministic**: Same source location always generates same IDs
- **Thread-safe**: No global state, no atomic operations
- **Salsa-compatible**: IDs are derived from interned locations
- **Debuggable**: IDs encode source location information

## Implementation

### Data Structures

#### MetaSlot
```rust
struct MetaSlot<'db> {
    ty: RcValue<'db>,
    solution: Option<Rc<Syntax<'db>>>,
    waiters: Vec<WaitingTask>,
    poisoned: bool,  // NEW: Error recovery flag
}
```

#### SolverState
```rust
pub struct SolverState<'db> {
    metas: HashMap<MetaVariableId, MetaSlot<'db>>,  // Changed from Vec
    dependencies: HashMap<MetaVariableId, HashSet<MetaVariableId>>,  // NEW: DAG
    local_counters: HashMap<Location, u16>,  // NEW: Per-location counters
}
```

### Key Methods

#### Fresh Meta Allocation
```rust
pub fn fresh_meta(&mut self, loc: Location, ty: RcValue<'db>) -> MetaVariableId {
    let local_index = self.local_counters.entry(loc).or_insert(0);
    let id = MetaVariableId::new(loc, *local_index);
    *local_index += 1;
    self.metas.insert(id, MetaSlot::new(ty));
    id
}

pub fn fresh_poisoned_meta(&mut self, loc: Location, ty: RcValue<'db>) -> MetaVariableId {
    // Same as fresh_meta but creates a poisoned slot
}
```

#### Cycle Detection
```rust
pub fn solve_checked(&self, meta: MetaVariableId, value: Rc<Syntax<'db>>) 
    -> Result<(), Vec<MetaVariableId>> 
{
    let deps = self.collect_dependencies(&value);
    self.check_cycle(meta, &deps)?;  // Fails if cycle detected
    // ... update dependencies and solve
}
```

#### Unification Short-Circuit
```rust
pub async fn unify(...) -> UnifyResult<'db> {
    // Check for poisoned metas BEFORE structural unification
    if let Value::Flex(flex) = &*lhs {
        if ctx.state.borrow().is_poisoned(flex.head.id) {
            return Ok(());  // Short-circuit
        }
    }
    // ... normal unification
}
```

#### Zonking
```rust
pub fn zonk<'db>(state: &SolverState<'db>, term: &Syntax<'db>) -> Rc<Syntax<'db>> {
    match &term.data {
        SyntaxData::Metavariable(id, args) => {
            match state.solution(*id) {
                Some(solution) => zonk(state, &solution),  // Replace with solution
                None => Rc::new(term.clone()),  // Leave unsolved/poisoned as-is
            }
        }
        // ... structural recursion
    }
}
```

## Testing

### Test Coverage
- ✅ Direct cycle detection (`?M := ?M`)
- ✅ Transitive cycle detection (`?M := ?N`, `?N := ?M`)
- ✅ Valid dependencies (no false positives)
- ✅ Poisoned meta creation and detection
- ✅ Location-derived ID uniqueness
- ✅ Zonking unsolved metas
- ✅ Zonking solved metas
- ✅ Zonking poisoned metas

## Future Work

1. **Location Tracking**: Add current location to elaboration context
2. **Error Reporting**: Collect and report poisoned metas with source locations
3. **Dependency Visualization**: Debug tool to visualize the meta dependency DAG
4. **Incremental Zonking**: Cache zonked terms to avoid redundant work

## References

- `crates/hwml-elab/src/engine.rs` - SolverState and cycle detection
- `crates/hwml-elab/src/unify.rs` - Poisoned meta short-circuit
- `crates/hwml-elab/src/zonk.rs` - Zonking implementation
- `crates/hwml-core/src/common.rs` - MetaVariableId definition
- `docs/salsa-location-architecture.md` - Location system design

