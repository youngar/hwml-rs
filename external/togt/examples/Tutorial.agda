module Tutorial where

{-@AGDA-}
open import Prelude

-- Inductive types are defined as follows
data Nat : Set where
   zero : Nat
   suc  : Nat -> Nat

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

-- We can define addition as follows
add : Nat -> Nat -> Nat
add zero n    = n
add (suc m) n = suc (add m n)

-- The proof of identity on the left is trivial 
add-zero-l : (n : _) -> add zero n == n
add-zero-l _ = refl

-- There is a built-in equality type with the J axiom
-- This is it's definition in Agda syntax:
-- data _==_ {A : Set}(x : A) : A -> Set where
--  refl : x == x
--
-- J : {A : Set} {x y : A}
--     (P : (x : A) (y : A) -> x == y -> Set) ->
--     (∀ z -> P z z refl) -> (p : x == y) -> P x y p

-- We use the J-rule to eliminate the equality witness (add-zero-r n)
add-zero-r : (n : _) -> add n zero == n 
add-zero-r zero = refl
add-zero-r (suc n) = J (\x y _ -> suc x == suc y)
                       (\z     -> refl)
                       (add-zero-r n)

-- Types may have parameters, but not indices,
-- so we need a little hackery to achieve this 
data Vec (n : Nat) (A : Set) : Set where
  nil'  : n == zero -> Vec n A
  cons' : {m : Nat} -> n == suc m -> A -> Vec m A -> Vec n A

nil : {A : Set} -> Vec zero A
nil = nil' refl

cons : {A : Set} {m : Nat} -> A -> Vec m A -> Vec (suc m) A
cons a as = cons' refl a as

-- With these we can define the length 3 vector [1,2,3]
vec123 : Vec three Nat
vec123 = cons one (cons two (cons three nil))

-- We can also define an append function
append : {m : Nat} {n : Nat} {A : Set} -> Vec m A -> Vec n A -> Vec (add m n) A
append {m} {n} {A} (nil' eq) bs = J (\x y _ -> Vec y A -> Vec x A) (\_ xs -> xs) (J (\x y _ -> add x n == add y n) (\z -> refl) eq) bs
append {m} {n} {A} (cons' eq a as) bs = cons' (J (\x y _ -> add x n == add y n) (\_ -> refl) eq) a (append as bs) 

