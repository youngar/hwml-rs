# Notes

## To Do
- Stupid environemtns
- Move the definition of Nat from examples to prelude
- Syntax (and probably values): the vector of arguments for a type constructor or data constructor should be a boxed slice, not a vector.
  - We can also probably add some helpful .into calls for the arguments passed into type_constructor_rc
- Case branch verification
    - verify that the branches have the right number of constructor arguments
    - verify that all cases are handled
    - verify that all constructors are for the datatype being matched
- termination checking
- datatype formation rules
    - positivity
    - non-recursive for hardware
- HW lambda checking
  - don't form illegal closures
- eval: clone the environment less
    - try to share the local environment between closures
    - e.g. keep a mutable local env, and a lazy RC env for handing to closures,
    - dirty RC env when mutating local env
- binders: encode in the datatype the number of binders to use when evaluating closures
- functional but in place: try to get mutable references to RC data (refcount == 1)
  - e.g. when substituting into a closure, if we're the only user, we can mutate in place
- sharing syntax while quoting values
  - everytime we quote a value, we get back a new syntax node, even if there is sharing for the value
  - consider mapping the value to the syntax node it quotes to (i.e. interning)
  - some other solution?
- consider adding a reify and reflect constructor to values for clarity with defunctionalized NBE 
- type checking not implemented yet
- fuzzing:
  - generate values: creates programs in normal form
  - eval(quote(values)) == values (values should not reduce in eval)
- core pretty printing: case statements
  - simplified motive printing for matches
  - if motive does not use variables, skips the binder
    - same for pi types
- add universe levels 
- support for global constants / delta expansion
  - needed for recursive function defintions
- recursive local let statements, how does that work?
  - kind of trivial to have a local value call itself
  - how do let statements work with conversion checking?
- implicit arguments!
  - how do they work with datatypes
- eval tests
  - every reduction kind
- quote tests
  - basic tests
  - eta long forms
- check tests
  - same as quote tests
- conversion checking does not support subtyping
  - blott threads around a bool for if we are subtyping or looking for a literal match
  - e.g. `U0` is convertible to `U1` but `\x => U0` is not convertible to `\x => U1`
  - seems to assume the check_nf for normals is always a literal match

- Environment: Global and Local
  - borrowing one blocks borrowing the other, so we have some bad global.clone()s
  - consider splitting this into two structs, or or some other solution
  - in check.rs -> TCEnvironment we are cloning the val::Environment
- Environment scope guard
  - something that can capture the depth and reset when done.
- Consider adding top level defintions to the printed core language
   - writing tests sucks right now to preload datatypes into the environment

- Conversion checking
  - case statements currently require branches to be in the same order.

## Completed
- case parsing/printing using semicolons
- Data Constructors should not use pi types for arguments.
  - we can fix this up when we work on adding telescopes for unification



datatype Option(t : Type) where
  | Some(t)
  | None


Option : Type -> Type
Some : {t : Type} -> t -> Option t
None : {t : Type} -> Option t

Option (%0 : Type): Type
Some : %0 -> Option %0
None : Option %0

Option<T>:None

[@Some arg] : #[Option T]
[@None] : #[Option T]


# Notes on Datatype representation
- Look at agda-core for inspiration

Telescopes
  - are a dependent list of types [a : Type, b : a, c : Singleton b]
  - effectively a type of sigma

TypeConstructors
   - have two telescopes
     - parameters
     - indices, contextually under the parameters
     - final type `Universe x`, all parameters have to be members Ux
  - types are formed by supplying all parameters and indices

 DataConstructors
 - have two telescopes:
   - parameters, matching the type constructor (should these be read from the TCon?)
   - arguments, representing the data they store
   - final type of the data constructor
  - data is formed
    - first, assume all type parameters are in scope
    - supplying just the arguments


TODO: pg 54 pdf/42 labeled, Cockx thesis, acceptance criteria for datatypes
- lets jot those down

## CONCERN: does quoting this work?
  - concern is that we evaluate the type of each argument under an empty context,
  supplying the concrete paramter.  But the parameter in `#[TC x]` x is only valid
  in a non-empty context.
```
X : Type
TC (x : X) : Type
\x => #[TC x]

X : Type
Y (x : X) : Type
TC (x : X) (y : Y x): Type
\x \y => #[TC x y]
```

## Example: Vector
```
data Vec (a : Type) : Nat -> Type :=
  | Nil  : Vec a 0
  | Cons : a -> n -> Vec a n -> Vec a (n + 1)

let invert_vec (n : Nat) (v : Vec Bool n): Vec Bool n :=
  match {
    | Nil => Nil
    | Cons x n xs => Cons (invert x) n (invert_vec xs)
  }


Represented as:
      Params     Indices
@Vec [a : Type] [l : Nat]
      Arguments
@Nil  []
@Cons [x : a]
```

Example: Implicit arguments on data constructors
```
data Foo : Nat -> Type :=
  | Bar : {N} -> Foo N
# N is not actually an argument to Bar
(Bar : Foo 31)
# can't pattern match N out of Bar:
match (Bar : Foo 31) with
  | Bar => ...
```




## Example: Eq

```
data Id (A : Type) (x : A) : A -> Type :=
  | Refl : Id A x x

(refl zero) : Id Nat zero zero

(\x => x match  (y : Nat) (x : Id Nat y y) => Nat {
  | Refl y => y
}) : Id Nat zero zero -> Nat
```

## Another?
```
data Foo : Nat -> Type :=
  | foo : Foo 0
  | bar : n -> Foo n

M : (n : Nat) -> Foo n -> Type.

x match M {
  | foo =>  ...
  | bar n => ... : M(\n, bar n : Foo n)
}

to find the type of the `bar n` branch we:
- need to call the motive
  - create a fresh variable for each index
  - create some scrutinee `bar n`
  - evaluate the motive on the index + scrutinee


```



Another way to view a telescope mapping f : ∆ → ∆′ is as a typed variant
of a substitution. In particular, if we have a term u : A with free variables
coming from ∆′, then we can apply the substitution [∆′  → f ∆] to it, replacing
the variables from ∆′ by the values given by f ∆, to get a term u′ with free
variables coming from ∆.Example 2.6. Suppose ∆ = (k : N) and ∆′ = (m n : N) and let f k =
(zero; suc k). We have ∆′ ` m + n : N, so applying the substitution [∆′  →f ∆] = [m  → zero; n  → suc k] gives us ∆ ` zero + suc k : N.

∆ = (k : N)
∆′ = (m n : N)
f : ∆ → ∆′
f : (k : N) → (m n : N)
f k = (zero; suc k)

[∆′  →f ∆] = [m  → zero; n  → suc k] gives us ∆ ` zero + suc k : N.

[∆′  →f ∆]
[(m n : N)  →f (k : N)]
[(m n : N)  →(zero; suc (k : N))]



TC : P -> I -> Ux
P |- DC : A -> TC P DCI

1. push params from concrete type
2. evaluate args to values
3. create variables for each arg
4. create instance of DC
5. evaluate motive with DC


