# Introduction to HWML

HWML is a hardware description language that lets you design digital circuits using dependent types. It combines the precision of formal verification with the practicality of modern HDLs.

## What Makes HWML Different

HWML uses dependent types to catch errors at compile time that other HDLs only find during simulation or synthesis. The type system ensures that your circuits are correct by construction.

The language has two syntaxes. The surface language is what you write. The core language is the internal representation used by the compiler. This documentation focuses on the surface language unless you're working on the compiler itself.

## A Simple Example

Here's a NOT gate in HWML.

```hwml
prim Bit : Signal

def not_gate (x : Bit) : Bit :=
  match x with
  | 0 => 1
  | 1 => 0
  end
```

The type system verifies that this function always returns a bit when given a bit. Pattern matching ensures all cases are covered.

## Where to Go Next

If you're new to HWML, start with the getting started guide. If you want to see what the language can do, check out the surface syntax reference. If you're working on the compiler, the internals section documents the core IR and type system.

