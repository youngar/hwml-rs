module Goal2_OutOfOrder_SigmaType where

record Sigma (A : Set) (B : A -> Set) : Set
record Sigma A B where
  constructor pair
  field
    fst : A
    snd : B fst

{-@AGDA-}
open Sigma

data Bool : Set where
  true : Bool
  false : Bool

if : (A : Bool -> Set) -> (b : Bool) -> A true -> A false -> A b
if _ true  x y = x
if _ false x y = y

postulate LHS : (B : Set) -> B       -> Set
postulate RHS : (A : Set) -> (a : A) -> LHS A a

-- Atoms
postulate F : Bool -> Set

postulate P : (X : Set) -> (x : X) -> Set

-- Shorthands --
U : Set
U = Sigma Bool (\_ -> Bool)

set'  : U
set'  = pair true true

El : U -> Bool
El u = if (\_ -> Bool) (fst u) true (snd u)
---------------------------------------------

mutual
  alpha : Bool -> U
  alpha x = _

  -- Constraints
  c1 : (P ((x : Bool) -> F (El (alpha x)) -> U) (\x -> \y -> set')) ->
       (P ((_ : Bool) -> F true           -> U) (\x -> \y -> alpha x))
  c1 x = x
