module Goal2_OutOfOrder where

data Bool : Set where
  true : Bool
  false : Bool

data BoolOp : Set where
  None  : BoolOp
  Some  : Bool -> BoolOp

get : BoolOp -> Bool
get None = true
get (Some x) = x

postulate LHS : (B : Set) -> B       -> Set
postulate RHS : (A : Set) -> (a : A) -> LHS A a

-- Atoms
postulate F : Bool -> Set
postulate P : (X : Set) -> (x : X) -> Set

mutual
  alpha : Bool -> BoolOp
  alpha x = _

  -- Constraints
  c1 : (P ((x : Bool) -> F (get (alpha x)) -> BoolOp) (\x -> \y -> None)) ->
       (P ((_ : Bool) -> F true            -> BoolOp) (\x -> \y -> alpha x))
  c1 x = x
