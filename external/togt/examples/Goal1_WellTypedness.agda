module Goal1_WellTypedness where

{-@AGDA-}
open import Prelude

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Bool : Set where
  true  : Bool
  false : Bool

F : Bool -> Set
F false = Bool
F true  = Nat

one : Nat
one = suc zero

two : Nat
two = suc (suc zero)

f : (b : _) -> F b -> Nat
f false false = zero
f false true  = one
f true  x     = two

-- data D : Nat -> Set where
--   mkD : (b : Bool) (x : F b) -> D (f b x)

postulate D : Nat -> Set
postulate mkD : (b : Bool) (x : F b) -> D (f b x)

mutual
  MX : Nat -> Set
  MX = _

  Mb : Nat -> Bool
  Mb = _

  -- Here we should check
  --    (n : Nat) -> ?X n == (x : F (?b 0)) -> D (f (?b 0) x)
  -- and get stuck on comparing the domains, but special inference
  -- for constructors is overeager and compares the target types,
  -- solving
  --    ?X : Nat -> Set
  --    ?X x := D (f (?b 0) x)
  -- Note that the call to f is not well-typed unless we solve the
  -- (as yet unsolved) constraint Nat == F (?b 0).
  constr1 : (n : Nat) -> MX n
  constr1 = mkD (Mb zero)

  -- Now we can form other constraints on ?X. This one simplifies to
  --   f (Mb 0) 1 == 0      (*)
  constr2 : MX one == D zero
  constr2 = refl

  -- Finally, we pick the wrong solution for ?b, causing (*) to become
  --   f false 1 ≡ 0
  -- which crashes with an __IMPOSSIBLE__ when we try to reduce the call to f.
  solve-b : Mb == (\_ -> false)
  solve-b = refl
