# HWML Language Features

This guide walks through the main features of HWML using working examples. Every code snippet here is typechecked by the compiler, so you can trust that the syntax is correct.

## Basic Definitions

Most HWML programs start by defining values. The `def` keyword introduces a new definition.

```hwml
prim Bit : Signal

def id (x : Bit) : Bit := x
```

Type annotations are optional when the compiler can infer them.

```hwml
prim Bit : Signal

def zero : Bit := 0
def one := 1
```

## Functions

Functions can take multiple parameters. You can write them with or without type annotations.

```hwml
prim Bit : Signal

def and_gate (a : Bit) (b : Bit) : Bit := a
def or_gate a b := a
```

Lambda syntax works too.

```hwml
prim Bit : Signal

def not_gate : Bit -> Bit := fun x => x
def xor_gate := fun a b => a
```

## Primitives

The `prim` keyword declares external types and values that the compiler knows about but doesn't define itself.

```hwml
prim Bit : Signal

def bit_zero : Bit := 0
def bit_one : Bit := 1
```

## Function Types

Function types use the arrow `->`. HWML supports dependent types, where the return type can depend on the value of a parameter.

```hwml
prim Bit : Signal

def identity_type := Bit -> Bit
def gate_type := Bit -> Bit -> Bit
def dependent_fn (x : Bit) : Bit -> Bit := fun y => y
```

## Hardware Arrow

The fat arrow `=>` distinguishes hardware module types from regular mathematical functions. This matters because hardware modules represent synthesizable circuits, not just computations.

```hwml
prim Bit : Signal

def hw_identity_type := Bit => Bit
def hw_gate_type := Bit => Bit => Bit
```

## Pattern Matching

Pattern matching uses the `match` keyword. Each branch starts with a pipe and ends with an arrow pointing to the result.

```hwml
prim Bit : Signal

def not_bit (b : Bit) : Bit :=
  match b with
  | 0 => 1
  | 1 => 0
  end
```

## Meta Definitions

Meta definitions run at compile time. They're useful for generating code or computing types.

```hwml
prim Bit : Signal

meta bit_type := Bit
meta make_identity (t : _) := fun (x : t) => x
```

## Let Expressions

Local bindings use `let ... in` syntax. Each binding is visible in the expressions that follow.

```hwml
prim Bit : Signal

def example (x : Bit) : Bit :=
  let y := x in
  let z := y in
  z
```

## Application

Function application is just whitespace. Write the function followed by its arguments.

```hwml
prim Bit : Signal

def identity (x : Bit) : Bit := x
def result := identity 0

def and_fn (a : Bit) (b : Bit) : Bit := a
def and_result := and_fn 0 1
```

## Grouping

Parentheses control precedence and grouping.

```hwml
prim Bit : Signal

def nested := (fun x => x) 0
def fn_type := (Bit -> Bit) -> Bit
```

## Parameter Styles

You can mix typed and untyped parameters however you want.

```hwml
prim Bit : Signal

def fn1 a b c := a
def fn2 (a : Bit) (b : Bit) (c : Bit) : Bit := a
def fn3 (a : Bit) b (c : Bit) := a
```

## Examples

```hwml
prim Bit : Signal

def id (x : Bit) : Bit := x
```

```hwml
prim Bit : Signal

def compose (f : Bit -> Bit) (g : Bit -> Bit) (x : Bit) : Bit :=
  f (g x)
```

```hwml
prim Bit : Signal

def const_zero : Bit := 0
def const_one : Bit := 1
def always_zero (x : Bit) : Bit := const_zero
```

