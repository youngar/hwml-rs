# HWML

[![CI](https://github.com/youngar/hwml-rs/actions/workflows/ci.yml/badge.svg)](https://github.com/youngar/hwml-rs/actions/workflows/ci.yml)

HWML is an in-development hardware description language equiped with a powerful metaprogramming layer.

```hwml
meta def option.map {a} {b} (f : ^a -> ^b)) (x : ^(option a)) : ^(option b) =
  match x with
    | some v => f v
    | none   => none
```

## Documentation
- [Development](./doc/Development.md)
