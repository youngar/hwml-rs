# Resolver Issue Summary

## The Problem

**When elaborating constant (def) definitions, the resolver is not updated to include the constant's namespace context.** This means identifiers in the constant's type or value expressions cannot properly resolve using the resolver's namespace hierarchy.

## Root Cause

The issue exists at the **call site** in `crates/hwml-elab/src/program.rs`:

### ❌ Current (Broken) - `elab_def_statement`

```rust
fn elab_def_statement<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    def: &hwml_surface::Def,
    resolver: &Resolver<'db>,  // ⚠️ Resolver from caller
    stub_table: &StubTable<'db>,
    decls: &mut Vec<ElaboratedDecl<'db>>,
    errors: &mut Vec<ElabError<'db>>,
) {
    let qname = bytes_to_simple_qname(db, resolver.namespace(), &def.id.value);
    
    let result: Result<ConstantInfo<'db>, ElabError<'db>> = {
        let mut state = SolverState::new();
        // ❌ BUG: Uses resolver directly without pushing namespace
        let mut elab = Elaborator::new(global, ElabCtx::empty(), &mut state, resolver, stub_table);
        elab::decl::elab_constant(db, &mut elab, def).and_then(|elaborated| {
            zonk(&mut state)?;
            let ty = substitute_metas_in_syntax(&elaborated.ty, &state);
            let val = substitute_metas_in_syntax(&elaborated.value, &state);
            Ok(ConstantInfo::new(ty, val))
        })
    };
    
    // ...
}
```

### ✅ Correct Pattern - `elab_inductive_statement`

```rust
fn elab_inductive_statement<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    ind: &hwml_surface::Inductive,
    resolver: &Resolver<'db>,
    stub_table: &StubTable<'db>,
    decls: &mut Vec<ElaboratedDecl<'db>>,
    errors: &mut Vec<ElabError<'db>>,
) {
    // ✅ Push namespace BEFORE creating elaborator
    let ind_path = util::surface_id_to_path(db, &ind.name)
        .ok_or_else(|| ElabError::NotInScope {
            name: String::from_utf8_lossy(&ind.name.value).to_string(),
            span: None,
        })?;
    let ind_resolver = resolver.push_namespace(db, &ind_path);
    
    // Phase 1: Elaborate header with updated resolver
    let mut header_state = SolverState::new();
    let mut elab = Elaborator::new(
        global,
        ElabCtx::empty(),
        &mut header_state,
        &ind_resolver,  // ✅ Uses updated resolver
        stub_table,
    );
    
    // Elaborate parameters, indices, constructors...
}
```

## Why Inductives Work But Constants Don't

### Inductives (✅ Correct)

1. `elab_inductive_statement` receives resolver from caller
2. **Pushes namespace** for the inductive type: `resolver.push_namespace(Foo.MyType)`
3. Creates `Elaborator` with updated resolver
4. When elaborating parameters/indices/constructors:
   - Identifiers first check local context
   - If not found locally, use `synth_global_by_path()` → `resolve_path()` 
   - Resolver walks scopes from `Foo.MyType` → `Foo` → root
   - ✅ Can find names in parent namespaces

### Constants (❌ Broken)

1. `elab_def_statement` receives resolver from caller
2. **Does NOT push namespace** for the constant
3. Creates `Elaborator` with unmodified resolver
4. When elaborating type/value expressions:
   - Identifiers first check local context
   - If not found locally, use `synth_global_by_path()` → `resolve_path()`
   - Resolver walks scopes from **caller's namespace** (not constant's namespace)
   - ❌ May fail to resolve names that should be in scope

## Impact

This bug affects:

1. **Constants in namespaces** that reference other names in the same namespace
2. **Constants with `open` statements** in their scope (if that feature exists)
3. **Consistency** between inductive and constant elaboration

## Example Scenario

```hwml
namespace Foo {
  def helper : Type = ...
  
  def myFunc : Type = helper  -- ❌ May fail to resolve 'helper'
}

// Compare with inductive (works correctly):
namespace Bar {
  inductive MyType : Type {
    constructor : helper -> MyType  -- ✅ Resolves 'helper' correctly
  }
}
```

## The Fix

Apply the same pattern used for inductives to constants:

```rust
fn elab_def_statement<'db, Db>(
    db: &'db Db,
    global: &mut GlobalEnv<'db>,
    def: &hwml_surface::Def,
    resolver: &Resolver<'db>,
    stub_table: &StubTable<'db>,
    decls: &mut Vec<ElaboratedDecl<'db>>,
    errors: &mut Vec<ElabError<'db>>,
) {
    // NEW: Extract constant's path and push namespace
    let def_path = util::surface_id_to_path(db, &def.id)
        .ok_or_else(|| ElabError::NotInScope {
            name: String::from_utf8_lossy(&def.id.value).to_string(),
            span: None,
        })?;
    let def_resolver = resolver.push_namespace(db, &def_path);
    
    let qname = bytes_to_simple_qname(db, resolver.namespace(), &def.id.value);
    
    let result: Result<ConstantInfo<'db>, ElabError<'db>> = {
        let mut state = SolverState::new();
        // FIX: Use updated resolver with constant's namespace
        let mut elab = Elaborator::new(global, ElabCtx::empty(), &mut state, &def_resolver, stub_table);
        elab::decl::elab_constant(db, &mut elab, def).and_then(|elaborated| {
            // ...
        })
    };
}
```

## Additional Fix Locations

The same fix is needed in:

1. **`crates/hwml-elab/src/scc_elab.rs`** - Phase 3 body elaboration for constants in SCCs
2. Any other places that elaborate constants (search for `elab_constant` calls)

## References

- **Correct pattern**: `crates/hwml-elab/src/program.rs:310-450` (`elab_inductive_statement`)
- **Broken pattern**: `crates/hwml-elab/src/program.rs:276-308` (`elab_def_statement`)
- **Inductive elaboration**: `crates/hwml-elab/src/elab/decl.rs:191-291` (shows namespace push in `elab_inductive_impl`)
- **Name resolution**: `crates/hwml-elab/src/elab/expr.rs:88-146` (shows how identifiers are resolved)
- **Resolver documentation**: `crates/hwml-elab/src/resolver.rs`
