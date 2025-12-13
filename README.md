# HWML

[![CI](https://github.com/youngar/hwml-rs/actions/workflows/ci.yml/badge.svg)](https://github.com/youngar/hwml-rs/actions/workflows/ci.yml)

HWML is an in-development hardware description language equipped with a powerful metaprogramming layer.

```hwml
meta def option.map (f : ^a -> ^b) (x : ^(option a)) : ^(option b) :=
  [
    x match {
      | some v => f v
      | none   => none
    }
  ]
```

## Documentation
- [Development](./doc/Development.md)
