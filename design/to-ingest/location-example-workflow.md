# Location Information - Complete Workflow Example

This document shows a concrete example of how locations flow through the entire HWML pipeline.

## Example Source File

**File**: `my-hardware/src/adder.hwml`  
**Library**: `my-hardware`  
**Content**:
```hwml
1  def half_adder (a b : Bit) : Bit × Bit :=
2    let sum := xor a b in
3    let carry := and a b in
4    (sum, carry)
```

## Step 1: Parser Creates Locations

```rust
// In hwml-surface parser
let source_text = "def half_adder (a b : Bit) : Bit × Bit := ...";
let line_info = LineInfo::from_bytes(source_text.as_bytes());

// Create SourceFileId
let lib_name = Word::new(db, "my-hardware");
let file_path = Word::new(db, "/workspace/my-hardware/src/adder.hwml");
let file_id = SourceFileId::new(db, lib_name, file_path);

// Parser encounters "def" token at byte offset 0
let (line, col) = line_info.loc(0);  // Returns (0, 0) - 0-based
let def_loc = Location::new(db, LocationData::FileLineCol {
    file: file_id,
    line: (line + 1) as u32,    // Convert to 1-based: line = 1
    column: (col + 1) as u32,   // Convert to 1-based: column = 1
});

// Parser encounters "half_adder" at byte offset 4
let (line, col) = line_info.loc(4);  // Returns (0, 4)
let id_loc = Location::new(db, LocationData::FileLineCol {
    file: file_id,
    line: 1,
    column: 5,  // "half_adder" starts at column 5
});

// Build surface Def node
let def_node = Def {
    loc: def_loc,  // Location, not Range<usize>!
    id: Id { loc: id_loc, value: "half_adder".into() },
    // ... rest of node
};
```

## Step 2: Elaborator Preserves Locations

```rust
// In hwml-elab
fn elab_constant<'db>(
    db: &'db dyn Database,
    elab: &mut Elaborator<'db>,
    def: &Def,
) -> Result<ConstantInfo<'db>, ElabError<'db>> {
    let name_loc = def.id.loc;  // Location from surface
    
    // Elaborate the type
    let ty_syntax = elab_type(db, elab, &def.ty)?;
    
    // Elaborate the value, preserving location
    let value_syntax = elab_expr(db, elab, &def.value)?;
    
    // Attach location to elaborated constant
    let constant = ConstantInfo {
        ty: ty_syntax.with_location(name_loc),  // Preserve location!
        value: value_syntax.with_location(name_loc),
    };
    
    Ok(constant)
}
```

## Step 3: Core IR Carries Locations

```rust
// In hwml-core Syntax
pub enum Syntax<'db> {
    Lambda(Location<'db>, Binding<RcSyntax<'db>>),
    App(Location<'db>, RcSyntax<'db>, RcSyntax<'db>),
    // Every variant has a Location as first field
}

impl<'db> Syntax<'db> {
    pub fn location(&self) -> Location<'db> {
        match self {
            Syntax::Lambda(loc, _) => *loc,
            Syntax::App(loc, _, _) => *loc,
            // ...
        }
    }
}

// Example: Creating a lambda during elaboration
let lambda_loc = expr.loc;  // From surface syntax
let core_lambda = Syntax::lambda_rc(lambda_loc, binding);
```

## Step 4: Location in Error Messages

```rust
// Type error during elaboration
fn check_application<'db>(
    db: &'db dyn Database,
    func: &RcSyntax<'db>,
    arg: &RcSyntax<'db>,
) -> Result<RcSyntax<'db>, TypeError<'db>> {
    let func_ty = infer_type(db, func)?;
    let arg_ty = infer_type(db, arg)?;
    
    match func_ty.as_ref() {
        Value::Pi(pi) => {
            if !types_equal(db, &pi.source, arg_ty) {
                return Err(TypeError {
                    location: arg.location(),  // Location from syntax!
                    expected: pi.source.clone(),
                    got: arg_ty.clone(),
                });
            }
            // ...
        }
        _ => return Err(TypeError {
            location: func.location(),
            // ...
        })
    }
}

// Display error
impl<'db> TypeError<'db> {
    pub fn display<Db>(&self, db: &'db Db) -> String
    where
        Db: salsa::Database,
    {
        format!(
            "{}: Type mismatch\n  Expected: {}\n  Got: {}",
            self.location.display(db),  // "adder.hwml:2:10"
            // ... format types
        )
    }
}

// Output:
// /workspace/my-hardware/src/adder.hwml:2:10: Type mismatch
//   Expected: Bit
//   Got: Bit × Bit
```

## Step 5: CIRCT Backend Consumes Locations

```rust
// In hwml-circt
pub fn translate_constant<'c, 'db>(
    ctx: &'c CirctContext,
    db: &'db dyn Database,
    name: QualifiedName<'db>,
    info: &ConstantInfo<'db>,
) -> Result<()> {
    // Get location from elaborated syntax
    let hwml_loc = info.value.location();
    
    // Convert to MLIR location
    let mlir_loc = ctx.to_mlir_location(db, hwml_loc);
    
    // Use in CIRCT operation
    let module_op = OperationBuilder::new("hw.module", mlir_loc)
        .add_attributes(...)
        .build()?;
    
    Ok(())
}

// CirctContext implementation
impl CirctContext {
    pub fn to_mlir_location<'db>(
        &self,
        db: &'db dyn Database,
        loc: Location<'db>,
    ) -> MlirLocationWrapper {
        match loc.data(db) {
            LocationData::FileLineCol { file, line, column } => {
                let path = file.canonical_path(db).text(db);
                
                // Create MLIR FileLineColLoc
                unsafe {
                    let filename_attr = mlirStringAttrGet(
                        self.context.as_raw(),
                        mlirStringRefCreateFromCString(path.as_ptr() as *const i8),
                    );
                    let raw = mlirLocationFileLineColGet(
                        self.context.as_raw(),
                        filename_attr,
                        *line,
                        *column,
                    );
                    MlirLocationWrapper::from_raw(raw)
                }
            }
            LocationData::Synthetic { label } => {
                // Use UnknownLoc for synthetic
                MlirLocationWrapper::unknown(&self.context)
            }
        }
    }
}
```

## Step 6: MLIR Output with Locations

Generated MLIR:
```mlir
module {
  hw.module @half_adder(%a: i1, %b: i1) -> (sum: i1, carry: i1) {
    %0 = comb.xor %a, %b : i1 loc("adder.hwml":2:16)
    %1 = comb.and %a, %b : i1 loc("adder.hwml":3:18)
    hw.output %0, %1 : i1, i1 loc("adder.hwml":4:5)
  } loc("adder.hwml":1:1)
}
```

Note the `loc("adder.hwml":2:16)` annotations - these came from our `Location` system!

## Step 7: Verilog Output with Comments

If CIRCT is configured to preserve locations:
```verilog
// Generated from adder.hwml:1:1
module half_adder(
  input  a,
  input  b,
  output sum,
  output carry
);

  assign sum = a ^ b;     // adder.hwml:2:16
  assign carry = a & b;   // adder.hwml:3:18

endmodule
```

## Synthetic Location Example

```rust
// Compiler generates a metavariable during elaboration
fn fresh_metavar<'db>(
    db: &'db dyn Database,
    state: &mut SolverState<'db>,
    ty: RcValue<'db>,
) -> RcSyntax<'db> {
    let id = state.fresh_meta_id();
    
    // Create synthetic location
    let label = Word::new(db, &format!("?{}", id.local_index));
    let loc = Location::new(db, LocationData::Synthetic { label });
    
    // Create metavariable syntax with synthetic location
    Syntax::metavar_rc(loc, id, ty)
}

// Display in errors:
// <metavar-?42>: Cannot infer type
```

## Location in .hwmli Files

When serializing to `.hwmli`:

```rust
// Serialize
let serialized = loc.serialize(db);
// Produces:
SerializedLocation::FileLineCol {
    library_name: "my-hardware".to_string(),
    file_path: "src/adder.hwml".to_string(),  // Relative path
    line: 2,
    column: 16,
}

// Deserialize in another compilation
let loc = Location::deserialize(db, &serialized);
// Reconstructs the same Location via interning
```

## Summary of Data Flow

```
Source File
    ↓ (parse)
Surface Syntax with Location
    ↓ (elaborate)
Core IR with Location
    ↓ (check)
Typed Core IR with Location
    ↓ (translate)
CIRCT IR with MlirLocation
    ↓ (export)
Verilog with comments
```

At every step, location information is preserved and enriched, enabling:
- **Precise error messages** pointing to exact source locations
- **Cross-library diagnostics** showing which library caused the error
- **Rich IDE support** for jump-to-definition, hover, etc.
- **Debuggable generated code** tracking back to source
