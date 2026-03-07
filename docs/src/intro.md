# Introduction to HWML

HWML is a hardware description language with two levels:
- **hwml** - The surface language (user-facing)
- **hwmlc** - The core language (internal representation)

## Type Constructors

```hwmlc
tcon @Bool : -> U0 where
  dcon @True : #[@Bool]
  dcon @False : #[@Bool]
;
```

## Hardware Bit Types

```hwmlc
const @BitZero : ^(^s Bit) = 0;
const @BitOne : ^(^s Bit) = 1;
```

## Type Errors

```hwmlc,should_fail
const @Bad : U0 = 0;
```

