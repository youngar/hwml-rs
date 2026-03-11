# Preprocessor Test Page

This page tests the mdbook-hwml preprocessor features.

## Session State Test

By default, code snippets on the same page share context. This allows you to build up definitions incrementally:

First, define a primitive type and value:

```hwmlc
prim $Nat : U0;
prim $zero : $Nat;
```

Then define some constants using that type:

```hwmlc
const @Zero : $Nat = $zero;
const @One : $Nat = $zero;
```

And continue building on those definitions:

```hwmlc
const @Two : $Nat = @Zero;
const @Three : $Nat = @One;
```

All three snippets above are type-checked together, so later snippets can reference earlier definitions.

## Hidden Lines Test

The following code block uses hidden lines (prefixed with `# `) to set up context:

```hwmlc
# prim $Bool : U0;
# prim $true : $Bool;
# prim $false : $Bool;
const @True : $Bool = $true;
const @False : $Bool = $false;
```

The reader should only see the `const` declarations, but the typechecker should see the `prim` declarations too.

## No Session Modifier

You can opt out of session state with the `no_session` modifier. This snippet is isolated:

```hwmlc,no_session
prim $Bit : U0;
prim $zero_bit : $Bit;
const @BitZero : $Bit = $zero_bit;
```

## Should Fail Test

This snippet is intentionally invalid and marked to fail:

```hwmlc,should_fail
this is not valid syntax at all!!!
```

## Ignore Test

This snippet is ignored (not type-checked):

```hwmlc,ignore
const @FutureFeature : $NotYetImplemented = $undefined;
```

## Multiple Hidden Lines

```hwmlc,no_session
# prim $Vec : U0;
# prim $nil : $Vec;
# prim $cons : $Vec;
const @VecTwo : $Vec = $nil;
const @VecThree : $Vec = $cons;
```

Only `VecTwo` and `VecThree` should be visible to readers.

