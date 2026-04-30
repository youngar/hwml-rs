{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS -fno-warn-orphans #-}
{-# OPTIONS -fno-warn-partial-type-signatures #-}
module Tog.Prelude
  ( module Prelude
#if __GLASGOW_HASKELL__ < 710
  , (Control.Applicative.<*>)
  , Control.Applicative.Applicative
  , Data.Foldable.Foldable
  , Data.Traversable.Traversable
  , Control.Applicative.pure
  , Data.Traversable.sequenceA
  , Data.Traversable.traverse
  , (Control.Applicative.<$)
  , (Control.Applicative.<$>)
#endif
  , (!!)
  , (Data.Function.&)
  , (Control.Arrow.***)
  , (Control.Arrow.>>>)
  , (Control.Monad.<=<)
  , (Data.Monoid.<>)
  , (Control.Applicative.<|>)
  , (Control.Monad.>=>)
  , Data.Bifunctor.Bifunctor(..)
  , Data.Collect.Collect(..)
  , Data.Collect.Collect_
  , Control.Applicative.Const(..)
  , Control.Monad.Trans.Except.ExceptT(..)
  , GHC.Generics.Generic
  , Data.Hashable.Hashable(..)
  , Data.String.IsString(..)
  , Control.Monad.Trans.Maybe.MaybeT(..)
  , Control.Monad.IO.Class.MonadIO(..)
  , Data.Monoid.Monoid(..)
  , Numeric.Natural.Natural
  , Data.Typeable.Typeable
  , Data.Either.Validation.Validation(..)
  , Control.Lens._1
  , Control.Lens._2
  , Control.Lens._3
  , Data.Foldable.any
  , Control.Monad.ap
  , Data.Maybe.catMaybes
  , Data.Ord.comparing
  , Data.Either.Validation.eitherToValidation
  , Data.List.elemIndex
  , Data.Foldable.fold
  , Data.Foldable.foldl'
  , Data.Foldable.foldlM
  , Data.Traversable.for
  , Data.Traversable.forM
  , Data.Foldable.forM_
  , Data.Maybe.fromMaybe
  , Data.List.groupBy
  , Control.Monad.guard
  , System.IO.hPutStr
  , System.IO.hPutStrLn
  , Data.List.intersperse
  , Data.Maybe.isJust
  , Data.Maybe.isNothing
  , Data.List.isPrefixOf
  , Control.Monad.join
  , length
  , Control.Monad.Trans.lift
  , Control.Monad.liftM
  , Control.Monad.liftM2
  , Control.Monad.mplus
  , Data.Foldable.msum
  , Control.Monad.mzero
  , Data.Function.on
  , Control.Lens.over
  , replicate
  , Control.Monad.Trans.Except.runExceptT
  , Data.List.sortBy
  , System.IO.stderr
  , strictDrop
  , strictSplitAt
  , Control.Monad.Trans.Except.throwE
  , Control.Monad.Trans.Except.catchE
  , Data.Foldable.toList
  , Debug.Trace.trace
  , traceM
  , Debug.Trace.traceShow
  , Control.Monad.unless
  , Data.Either.Validation.validationToEither
  , Control.Monad.void
  , Control.Monad.when
  , Control.Lens.makeLenses
  , Control.Lens.use
  , (Control.Lens.%=)
  , (Control.Lens..=)
  , (Control.Lens.^.)
  , Control.Lens.zoom
  , Control.Lens.Lens'
  , Control.Lens.Getter
  , pattern (:∋), (:∋), (:∈)(..)
  , CmdModule(..)
  , documentModules
  , Bwd(..)
  , Control.DeepSeq.NFData(rnf)
  , Control.DeepSeq.force
  , module Data.ISet
  , module Data.BitSet
  , module Data.Constraint
  , ConstraintK, TypeK
  , Data.Monoid.Any(..)
  , memptyM, MonoidM(..)
  , module Control.Monad.Identity
  , module Control.Monad.Writer.Strict
  , DefaultM(..) 
  , (Control.Lens.<&>)
  , (>&>)
  , Text.Read.readMaybe
  , enumAll
  , iterateN
  , Nat
  , natToInt
  , Data.Coerce.coerce
  , Data.Text.Text
  , Data.Aeson.ToJSON
  , Data.Aeson.FromJSON
  , module Algebra.Lattice
  , module Data.Sequence
    -- * Annotations
  , (:@)
  , pattern (:@)
  , Annotated(..)
    -- * Tagged
  , Tagged(..)
  , fromList
    -- * Monadic
  , evalWriterT
  , notImplemented
  , andM, orM
  ) where

import Prelude hiding (replicate, (!!), length, any, pi, exp, head, tail)

import qualified Control.Applicative
import qualified Control.Arrow
import qualified Control.Lens
import qualified Control.Monad
import qualified Control.Monad.IO.Class
import qualified Control.Monad.Trans
import qualified Control.Monad.Trans.Except
import qualified Control.Monad.Trans.Maybe
import qualified Data.Bifunctor
import qualified Data.Collect
import qualified Data.Either.Validation
import qualified Data.Foldable
import qualified Data.Function
import qualified Data.Hashable
import qualified Data.List hiding (head,tail)
import qualified Data.Maybe
import qualified Data.Monoid
import qualified Data.Ord
import qualified Data.String
import qualified Data.Traversable
import qualified Data.Typeable
import qualified Debug.Trace
import qualified GHC.Generics
import qualified Numeric.Natural
import qualified System.IO hiding (writeFile)
import qualified Control.DeepSeq
import qualified Text.Read
import qualified Data.Coerce
import qualified Data.Text
import qualified Data.Aeson
import           Data.Tagged (Tagged(..))
import           GHC.Exts (IsList(..))

import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Identity (Identity(..), runIdentity)
import Control.Monad.Writer.Strict (MonadWriter(..), runWriterT, WriterT, tell, execWriterT, listen, censor)
import Data.Monoid ((<>), Any(..))
import Control.Monad (liftM2)
import Data.List (intercalate)
import Data.Vector (Vector)
import Data.Hashable (Hashable, hashWithSalt)
import qualified Data.Vector as V
import Data.ISet (ISet, ISetMember, ISetMemberM)
import Data.BitSet (BitSet)

import Data.Constraint (Dict(..), (:=>), (:-)(..), (\\))
import qualified Data.Kind
import Data.Sequence (Seq, (<|), (|>))

import Algebra.Lattice hiding (meet, join)
import Development.Placeholders (placeholderNoWarning)

type ConstraintK = Data.Kind.Constraint
type TypeK = Data.Kind.Type


traceM :: (Monad m) => String -> m ()
traceM string = Debug.Trace.trace string $ return ()

length :: [a] -> Numeric.Natural.Natural
length []       = 0
length (_ : xs) = 1 + length xs

(!!) :: [a] -> Numeric.Natural.Natural -> a
(x : _ ) !! 0 = x
(_ : xs) !! n = xs !! (n - 1)
[]       !! _ = error "Prelude.Extended.!!: out of bounds"

replicate :: Numeric.Natural.Natural -> a -> [a]
replicate 0 _ = []
replicate n x = x : replicate (n-1) x

strictSplitAt :: Numeric.Natural.Natural -> [a] -> ([a], [a])
strictSplitAt 0 xs       = ([], xs)
strictSplitAt _ []       = error "strictSplitAt: list too short"
strictSplitAt n (x : xs) = let (l, r) = strictSplitAt (n-1) xs in (x : l, r)

strictDrop :: Numeric.Natural.Natural -> [a] -> [a]
strictDrop 0 xs       = xs
strictDrop _ []       = error "strictDrop: list too short"
strictDrop n (_ : xs) = strictDrop (n-1) xs

-- | Notation for type membership
--   Prevents bugs from swapping terms and their types in function calls
--   (and looks cool)
--
--   Be aware that this may introduce extra laziness.
{-# COMPLETE (:∈) #-}
{-# COMPLETE (:∋) #-}
data a :∈ b = a :∈ b deriving (Eq, GHC.Generics.Generic)
instance (Hashable a, Hashable b) => Hashable (a :∈ b)
type b :∋ a = a :∈ b

pattern (:∋) :: b -> a -> a :∈ b
pattern b :∋ a = a :∈ b

-- | Specifies command-line flag options in a way that is easy to
--   - Select from the program code, given a flag
--   - Display in a help message

data CmdModule a = CmdModule {
  opt      :: String
 ,name     :: String
 ,cmd      :: a
 }

documentModules :: [CmdModule a] -> String
documentModules cmdModules = intercalate ", "$ [opt <> " (" <> name <> ")" | CmdModule{opt,name} <- cmdModules]

-- | Reversed lists
--   Conor https://mail.haskell.org/pipermail/haskell-cafe/2007-July/029485.html
data Bwd x = B0 | Bwd x :. x
             deriving (Functor, Foldable, Traversable)

instance Semigroup (Bwd x) where
  (<>) x  B0        = x
  (<>) ys (xs :. x) = (<>) ys xs :. x
instance Monoid (Bwd x) where
  mempty = B0


instance IsList (Bwd x) where
  type Item (Bwd x) = x
  toList   = Data.Foldable.toList
  fromList = go . reverse
    where
      go []     = B0
      go (x:xs) = go xs :. x

instance Hashable a => Hashable (Vector a) where
  hashWithSalt s = hashWithSalt s . V.toList

-------------
-- MonoidM --
-------------

-- | A short-circuiting monoid instance
-- 
--   prop>  mappendM (pure a) (pure b) = pure (mappendM a b)
--   prop>  mconcatM . map pure = pure . mconcat
class Monoid a => MonoidM a where
  mappendM :: (Monad m) => m a -> m a -> m a
  mappendM = liftM2 mappend

  mconcatM :: (Monad m) => [m a] -> m a
  mconcatM [] = memptyM 
  mconcatM (a:[]) = a
  mconcatM (a:as) = mappendM a (mconcatM as) 

memptyM :: (Applicative m, Monoid a) => m a
memptyM = pure mempty

instance MonoidM Any where
  mappendM a b = a >>= \case
    x@(Any True) -> return x
    Any False    -> b

instance MonoidM (ISet a)

----------------------
-- Monadic defaults
----------------------

class DefaultM m a where
  defM :: m a

instance Applicative m => DefaultM m () where defM = pure ()

(>&>) :: Functor f => (a -> f b) -> (b -> c) -> a -> f c
(>&>) = flip$ fmap . fmap

----------------------
-- Enumerations
----------------------

enumAll :: (Enum a, Bounded a) => [a]
enumAll = [minBound..]

{-# INLINE iterateN #-}
iterateN :: Numeric.Natural.Natural -> (a -> a) -> (a -> a)
iterateN 0 _ x = x
iterateN 1 f x = f x   -- shortcut
iterateN n f x = f (iterateN (n-1) f x)


type Nat = Numeric.Natural.Natural

natToInt :: Nat -> Int
natToInt = fromIntegral 

--------------------------
-- MonadWriter
--------------------------

evalWriterT :: Functor m => WriterT w m a -> m a  
evalWriterT = runWriterT >&> fst

--------------------------
-- Annotated types
--------------------------

data Annotated b a = Annotated { annotation :: b
                               , annValue   :: a
                               }
  deriving (Show, Functor)

instance Monoid b => Applicative (Annotated b) where
  pure = (:@ mempty)
  (f :@ a) <*> (x :@ b) = f x :@ (a <> b)

type a :@ b = Annotated b a

{-# COMPLETE (:@) #-}
pattern (:@) :: a -> b -> a :@ b
pattern a :@ b = Annotated b a

instance Eq a => Eq (Annotated b a) where (==) = (==) `Data.Function.on` annValue
instance Ord a => Ord (Annotated b a) where compare = compare `Data.Function.on` annValue

------------
-- Tagged
------------
deriving instance Hashable a => Hashable (Tagged c a)

notImplemented :: _
notImplemented = placeholderNoWarning "Unimplemented feature"

----------------------------------------
-- Shortcircuiting monadic operations
----------------------------------------
{-# INLINE orM #-} 
orM :: Monad m => [m Bool] -> m Bool
orM [] = pure False
orM [m] = m
orM [a,b] = a >>= \case
  False -> b
  True  -> pure True
orM (a:as) = orM [a,orM as]

{-# INLINE andM #-} 
andM :: Monad m => [m Bool] -> m Bool
andM [] = pure True
andM [m] = m
andM [a,b] = a >>= \case
  True  -> b
  False -> pure False
andM (a:as) = andM [a,andM as]


