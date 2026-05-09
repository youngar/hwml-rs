# Parser Migration Guide - Line:Column Tracking

**Date:** 2026-05-05  
**Status:** In Progress

This guide shows how to migrate surface syntax nodes to use Line:Column tracking.

---

## Migration Pattern

### Step 1: Update Syntax Struct

**Before:**
```rust
#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Def {
    pub loc: Range<usize>,
    pub id: Id,
    pub bindings: Bindings,
    pub ty: Option<Box<Expression>>,
    pub value: Box<Expression>,
}
```

**After:**
```rust
#[derive(Clone, Eq, PartialEq, Debug, Hash)]
pub struct Def {
    pub loc: Range<usize>,           // Old (keep for backward compat)
    pub line_col: LineColRange,       // New (preferred)
    pub id: Id,
    pub bindings: Bindings,
    pub ty: Option<Box<Expression>>,
    pub value: Box<Expression>,
}

impl Def {
    /// Old constructor (deprecated)
    pub fn new(loc: Range<usize>, id: Id, bindings: Bindings, 
               ty: Option<Box<Expression>>, value: Box<Expression>) -> Self {
        Def {
            loc,
            line_col: LineColRange::new(0, 0, 0, 0),
            id,
            bindings,
            ty,
            value,
        }
    }

    /// New constructor using line:column
    pub fn new_with_line_col(line_col: LineColRange, id: Id, bindings: Bindings,
                             ty: Option<Box<Expression>>, value: Box<Expression>) -> Self {
        Def {
            loc: 0..0,
            line_col,
            id,
            bindings,
            ty,
            value,
        }
    }
}
```

---

### Step 2: Update Grammar Rule

**Before:**
```lalrpop
Def: Def = {
    <l:@L> "def" <id:Id> <bs:OptionalBindings> <t:(":" Expr0)?> ":=" <v:Expr0> <r:@R> => {
        Def::new(l..r, id, bs, t.map(|(_, ty)| ty), v)
    }
};
```

**After:**
```lalrpop
Def: Def = {
    <l:@L> "def" <id:Id> <bs:OptionalBindings> <t:(":" Expr0)?> ":=" <v:Expr0> <r:@R> => {
        let line_col = LineColRange::from_byte_range(l, r, ctx);
        Def::new_with_line_col(line_col, id, bs, t.map(|(_, ty)| ty), v)
    }
};
```

**Or inline:**
```lalrpop
Def: Def = {
    <l:@L> "def" <id:Id> <bs:OptionalBindings> <t:(":" Expr0)?> ":=" <v:Expr0> <r:@R> => {
        let (sl, sc, el, ec) = ctx.range_to_line_col(l, r);
        let line_col = crate::syntax::LineColRange::new(sl, sc, el, ec);
        Def::new_with_line_col(line_col, id, bs, t.map(|(_, ty)| ty), v)
    }
};
```

---

## Remaining Work

### Syntax Nodes to Migrate (in order of priority):

1. **High Priority** (used in error messages):
   - [x] `Namespace` ✅ (done)
   - [ ] `Def`
   - [ ] `Prim`
   - [ ] `Inductive`
   - [ ] `Constructor`

2. **Medium Priority** (expressions):
   - [ ] `Pi`
   - [ ] `Arrow`
   - [ ] `FatArrow`
   - [ ] `App`
   - [ ] `Fun`
   - [ ] `LetIn`
   - [ ] `Match`

3. **Low Priority** (terminals):
   - [ ] `Id`
   - [ ] `Num`
   - [ ] `Str`
   - [ ] `Universe`
   - [ ] `Underscore`
   - [ ] `Paren`

4. **Enums to update**:
   - [ ] `OpenModifier` variants
   - [ ] `Expression` variants (or add wrapper with location)

---

## Testing

After each migration, verify with:

```rust
#[test]
fn test_def_line_col_tracking() {
    let input = b"def foo := 42";
    let program = parse(input).unwrap();
    
    match &program.statements[0] {
        Statement::Def(def) => {
            // Should have actual line:column, not zeros
            assert_ne!(def.line_col.start_line, 0);
            assert_ne!(def.line_col.end_line, 0);
            
            // Should be on line 1 (0-based = line 0)
            assert_eq!(def.line_col.start_line, 0);
            assert_eq!(def.line_col.start_column, 0);
        }
        _ => panic!("Expected Def"),
    }
}
```

---

## Future Cleanup

Once all syntax nodes are migrated:

1. Remove `pub loc: Range<usize>` fields
2. Rename `new_with_line_col()` → `new()`
3. Remove old `new()` constructors
4. Update all downstream code using `.loc` to use `.line_col`

---

## Integration with hwml-core::Location

After surface syntax migration, create `Location<'db>` in elaboration:

```rust
// In elaboration code:
fn elaborate_def<'db>(
    db: &'db dyn salsa::Database,
    file: SourceFileId<'db>,
    def: &hwml_surface::Def,
) -> (RcSyntax<'db>, Location<'db>) {
    // Convert surface LineColRange → core Location
    let loc = Location::file_range_values(
        db,
        file,
        (def.line_col.start_line + 1) as u32,    // Convert 0-based → 1-based
        (def.line_col.start_column + 1) as u32,
        (def.line_col.end_line + 1) as u32,
        (def.line_col.end_column + 1) as u32,
    );
    
    // Elaborate and attach location
    let core_syntax = elaborate_def_impl(db, def);
    (core_syntax, loc)
}
```

