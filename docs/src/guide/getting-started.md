# Getting Started with HWML

This guide will help you write your first hardware circuit in HWML.

## Your First Circuit

The simplest circuit is just a wire that passes a signal through unchanged.

```hwml
prim Bit : Signal

def wire (x : Bit) : Bit := x
```

This defines a function called `wire` that takes a bit and returns it. The `prim Bit : Signal` line tells the compiler that `Bit` is a primitive signal type.

## Building a NOT Gate

A NOT gate inverts its input. We can define it using pattern matching.

```hwml
prim Bit : Signal

def not_gate (x : Bit) : Bit :=
  match x with
  | 0 => 1
  | 1 => 0
  end
```

The `match` expression checks the value of `x`. If it's 0, the result is 1. If it's 1, the result is 0.

## Next Steps

Now that you've seen the basics, you can explore more features in the reference documentation.

