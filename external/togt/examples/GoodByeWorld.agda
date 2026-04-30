module GoodByeWorld where

data Nat : Set where
   zero : Nat
   suc  : Nat -> Nat

data Bool : Set where
   true  : Bool
   false : Bool


wrong : Nat
wrong = true
