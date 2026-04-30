# Tog⁺ - A prototypical implementation of dependent types

Tog⁺ (pronounced tog-tee) is a prototype of a dependent type
checker using twin types. 

It is a variant/extension of [Tog][1].

## Compilation and usage 

1. Open the directory containing this file in a terminal/command-line prompt.

2. Download and install `stack`
   In Unix-y sytems:

    ```
    curl -sSL https://get.haskellstack.org/ | sh
    ```

   For Windows systems and others, check the [Stack user manual][2].

3. In the directory containing this file, run:

    ```
    stack install alex happy
    stack build
    ```

   This will take a while.  

4. To run Tog⁺, use:

    ```
    stack exec -- tog [OPTIONS] [FILE]
    ```

## Running examples

The `examples/` directory contains some examples and benchmarks.

- examples/Goal1_WellTypedness.agda
- examples/Goal2_OutOfOrder.agda
- examples/Language_test0_Type.agda
- examples/Language_test1_Pointed.agda
- examples/Language_test2_Subset.agda
- examples/Language_test3_Multigraph.agda
- examples/Language_test4_ReflGraph.agda
- examples/Language_test5_Precategory.agda
- examples/Language_test6_Setoid.agda

To run them, go to the directory containing this file after having compiled Tog⁺, and call:

```
stack exec tog -- [OPTIONS] [FILE]
```

…where `[FILE]` is the path to one of the above files, and `[OPTIONS]`
is one of the following configurations:

* Tog⁺ (recommended): `--synEquality 2 --physicalEquality --solver W --noCheckElaborated --fastElaborate --termType HC4`
* Tog⁺ without the syntactic equality rule: `--solver W --noCheckElaborated --fastElaborate --termType HC4 --synEquality 0`                   

For instance, in order to run the Setoid example from the main directory:  

`stack exec tog -- --synEquality 2 --physicalEquality --solver W --noCheckElaborated --fastElaborate --termType HC4 examples/Language_test6_Setoid.agda`

To compare with Agda (tested with v2.6.1), install [Agda][3] and then run:

`agda -iexamples -iagda-prelude --type-in-type --without-K --no-termination-check --ignore-interfaces --no-positivity-check [FILE]`

### Helper scripts

*Alternatively*, if you are in a Unix-y system, you can run the examples
using one of the included shell scripts.

These scripts also enable the "-s" flag in the Haskell RTS so that CPU and
memory usage statistics will be output.

* Tog⁺ (recommended): `./togt.sh [FILE]`
* Tog⁺ without the syntactic equality rule: `./togt-nosyneq.sh [FILE]`
* Agda: `./agda-tog-compat.sh [FILE]`

[1]: https://github.com/bitonic/tog
[2]: https://docs.haskellstack.org/en/stable/README/
[3]: http://agda-lang.org/
