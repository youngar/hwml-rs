{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Tog.Unify.Algebra (
  -- * Unifier class
    Alg(..)
  , algCountLeaves
  , pattern Top
  , (>>:), solved, unConj
  ) where

import           Tog.Prelude

import           Tog.Term
import           Data.Sequence (Seq)

import           Tog.PrettyPrint                  (($$), (//>), group, indent)
import qualified Tog.PrettyPrint                  as PP

import qualified Data.Foldable as F

import           Data.FreeLattice (pattern Top, DecTop(..))
import           Data.Generics.Is.TH (isP)

data Alg a =
             Base a 
           | Conj (Seq (Alg a))
           | Alg a :>>: Alg a
           deriving (Functor, Foldable, Traversable)

instance MeetSemiLattice (Alg a) where
  Top    /\ b      = b
  a      /\ Top    = a
  Conj a /\ Conj b = Conj (a <> b)
  a      /\ Conj b = Conj (a <| b)
  Conj a /\      b = Conj (a |> b)
  a      /\      b = Conj [a,b]

instance BoundedMeetSemiLattice (Alg a) where top = Conj []
instance DecTop (Alg a) where isTop = $(isP [p| Conj [] |])

instance Semigroup (Alg a) where
  (<>) = (/\)

-- | We priorize conjunction, since that is the most common use case
instance Monoid (Alg a) where           
  mempty  = solved
  mconcat = meets 

-- | asConj
unConj :: Alg a -> [Alg a]
unConj (Conj cs) = toList cs 
unConj c         = [c]

-- | Constraint sequencing, associated to the right
(>>:) :: Alg a -> Alg a -> Alg a
Top        >>: x  = x
(x :>>: y) >>: z  = x >>: (y :>>: z)
x          >>: y  = x :>>: y

-- | Nothing left to do
solved :: Alg a
solved = Top

-- | Simplifying a constraint set
simplify :: Alg t -> Alg t
simplify (Conj cs)    = meets$ toList$ fmap simplify cs
simplify (c1 :>>: c2) = case simplify c1 of
  Top  -> simplify c2
  c1'  -> c1' >>: c2
simplify c@Base{}   = c

algCountLeaves :: Alg a -> Int  
algCountLeaves = F.length 

instance PrettyM t a => PrettyM t (Alg a) where
  prettyM Top = return "⊤" 
  prettyM (c1 :>>: c2 ) = do
        c1Doc <- prettyM c1
        c2Doc <- prettyM c2
        return $ group (indent 2 (group c1Doc) $$ ">>" $$ indent 2 (group c2Doc))
  prettyM (Base a) = prettyM a
  prettyM (Conj cs) = do
        csDoc <- mapM prettyM cs
        return $
          "Conj" //> PP.list (toList csDoc)


