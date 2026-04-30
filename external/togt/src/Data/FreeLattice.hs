{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS -Wno-orphans #-}
module Data.FreeLattice (
   evaluate
  ,simplify
  ,inj
  ,FreeLattice
  ,FreeLatticeBase(..)
   -- * Pattern synonyms for Top and Bottom
   --   
   --   This is a poor-man’s substitute for type classes with pattern synonyms.
  ,pattern Top
  ,pattern Bottom
  ,DecTop(..)
  ,DecBottom(..)
  ,prettyPrecFLM
  ,joinsM
  ,meetsM
  ,censorJoin
  ,fromBool
  ) where

import Data.Sequence (Seq, (|>), (<|))
import qualified Data.Sequence as Seq

import Algebra.Lattice
import Data.Foldable (toList)
import Data.Monoid ((<>))

import Data.Generics.Is.TH (isP)

import Control.Monad.Writer (MonadWriter(..), censor)

import qualified Tog.PrettyPrint                  as PP
import           Tog.Prelude (MonoidM(..))

data FreeLattice a = JoinAll (Seq (FreeLattice a))
                   | MeetAll (Seq (FreeLattice a))
                   | Base  a
                deriving (Functor, Foldable, Traversable)

class BoundedJoinSemiLattice a => DecBottom a where
  isBottom :: a -> Bool 
  default isBottom :: (Eq a) => a -> Bool
  isBottom = (== bottom)

class BoundedMeetSemiLattice a => DecTop a where
  isTop :: a -> Bool 
  default isTop :: (Eq a) => a -> Bool
  isTop = (== top)

pattern Bottom :: (DecBottom a) => a
pattern Bottom <- (isBottom -> True)
  where Bottom =  bottom

pattern Top :: (DecTop a) => a
pattern Top <- (isTop -> True)
  where Top =  top

meetsM :: (DecBottom a, BoundedMeetSemiLattice a, Monad m) => [m a] -> m a
meetsM [] = pure top
meetsM [ma] = ma
meetsM (ma:mas) = do
  ma >>= \case
    Bottom -> pure Bottom
    a      -> (a /\) <$> meetsM mas

joinsM :: (DecTop a, BoundedJoinSemiLattice a, Monad m) => [m a] -> m a
joinsM [] = pure bottom
joinsM [ma] = ma
joinsM (ma:mas) = do
  ma >>= \case
    Top -> pure Top
    a     -> (a \/) <$> joinsM mas

inj :: a -> FreeLattice a
inj = Base

evaluate :: BoundedLattice a => FreeLattice a -> a
evaluate (Base a) = a
evaluate (JoinAll as) = joins $ map evaluate $ toList as
evaluate (MeetAll as) = meets $ map evaluate $ toList as

simplify :: FreeLatticeBase a => FreeLattice a -> FreeLattice a
simplify (Base a)   = Base a
simplify (JoinAll as) =
  let (bases, rest) =
       let go [] = ([],[])
           go (Base e:zs) = let ~(xs,ys) = go zs in (e:xs,  ys)
           go (     r:zs) = let ~(xs,ys) = go zs in (  xs,r:ys)
       in
       go $ fmap simplify $ toList as
  in
  simpleJoin bases \/ joins rest

simplify (MeetAll as) =
  let (bases, rest) =
       let go [] = ([],[])
           go (Base e:zs) = let ~(xs,ys) = go zs in (e:xs,  ys)
           go (     r:zs) = let ~(xs,ys) = go zs in (  xs,r:ys)
       in
       go $ fmap simplify $ toList as
  in
  simpleMeet bases /\ meets rest

-- | This class enables deep simplification of the elements of a free lattice
class FreeLatticeBase a where
  simpleMeet :: [a] -> FreeLattice a
  simpleMeet = MeetAll . Seq.fromList . fmap Base

  simpleJoin :: [a] -> FreeLattice a
  simpleJoin = JoinAll . Seq.fromList . fmap Base

instance FreeLatticeBase a => DecBottom (FreeLattice a) where isBottom = $(isP [p| JoinAll [] |])
instance FreeLatticeBase a => DecTop    (FreeLattice a) where isTop    = $(isP [p| MeetAll [] |])
  
instance FreeLatticeBase a => MeetSemiLattice (FreeLattice a) where
  Bottom      /\ _           = Bottom
  _           /\ Bottom      = Bottom
  Base a      /\ Base b      = simpleMeet [a,b]
  (MeetAll a) /\ (MeetAll b) = MeetAll (a <> b)
  (MeetAll a) /\ b           = MeetAll (a |> b)
  a           /\ (MeetAll b) = MeetAll (a <| b)
  a           /\ b           = MeetAll [a,b]

instance FreeLatticeBase a => BoundedMeetSemiLattice (FreeLattice a) where top    = MeetAll []

instance FreeLatticeBase a => JoinSemiLattice (FreeLattice a) where
  Top         \/ _           = Top                                                      
  _           \/ Top         = Top                                                      
  Base a      \/ Base b      = simpleJoin [a,b]
  (JoinAll a) \/ (JoinAll b) = JoinAll (a <> b)
  (JoinAll a) \/ b           = JoinAll (a |> b)
  a           \/ (JoinAll b) = JoinAll (a <| b)
  a           \/ b           = JoinAll [a,b]

instance FreeLatticeBase a => BoundedJoinSemiLattice (FreeLattice a) where bottom = JoinAll []

instance FreeLatticeBase a => Lattice (FreeLattice a) where
instance FreeLatticeBase a => BoundedLattice (FreeLattice a) where

prettyPrecFLM :: Applicative m => (Int -> a -> m PP.Doc) -> Int -> FreeLattice a -> m PP.Doc
prettyPrecFLM f p (JoinAll mvs)
  | null mvs  = pure "⊥"
  | otherwise = PP.condParens (p > 3) . PP.separated "∨" <$> traverse (prettyPrecFLM f 3) (toList mvs)

prettyPrecFLM f p (MeetAll mvs)
  | null mvs  = pure "⊤"
  | otherwise = PP.condParens (p > 4) . PP.separated "∧" <$> traverse (prettyPrecFLM f 4) (toList mvs)

prettyPrecFLM f p (Base mvs)  = f p mvs

instance (DecBottom a, BoundedMeetSemiLattice a) => MonoidM (Meet a) where
  mappendM ma mb = ma >>= \case
    a@(Meet Bottom) -> pure a
    a               -> (a <>) <$> mb

-- Note that it does not fulfil the deMorgan laws
flipLattice :: (DecBottom a, DecTop a) => a -> a
flipLattice Bottom = Top
flipLattice Top    = Bottom
flipLattice bs     = bs

-- | Helper function for reporting ocurrences together with blocking
censorJoin :: (Functor f, JoinSemiLattice a, MonadWriter (f a) m) => a -> m b -> m b
censorJoin a =  censor (fmap (\/ a))

