module HelloWorld where

data Nat : Set where
   zero : Nat
   suc  : Nat -> Nat

one : Nat
one = suc zero

add : Nat -> Nat -> Nat
add zero n    = n
add (suc m) n = suc (add m n)
