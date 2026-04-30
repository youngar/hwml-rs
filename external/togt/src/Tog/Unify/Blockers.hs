module Tog.Unify.Blockers where

import qualified Data.Set                         as Set
import           Data.Set (Set)

import Tog.Term
import Control.Lens ((<&>))

import           Tog.PrettyPrint                  ((<+>))

data Blockers = AnyOf !(Set Blockers)
              | AllOf !(Set Blockers)
                -- ^ This does not block if the list is empty
              | AnyMeta Guard
              deriving (Eq, Ord)

shouldAttempt :: (MonadTerm t m) => Blockers -> m Bool
shouldAttempt (AnyOf mvs) | null mvs = return False
shouldAttempt (AnyOf mvs) = or <$> mapM shouldAttempt (Set.toList mvs)
shouldAttempt (AllOf mvs) | null mvs = return True
shouldAttempt (AllOf mvs) = and <$> mapM shouldAttempt (Set.toList mvs)
shouldAttempt (AnyMeta mvs) = guardIsInstantiated mvs

instance PrettyM t Blockers where
  prettyM (AnyOf mvs) = prettyM (Set.toList mvs) <&> \doc -> "any(" <+> doc <+> ")"
  prettyM (AllOf mvs) = prettyM (Set.toList mvs) <&> \doc -> "all(" <+> doc <+> ")"
  prettyM (AnyMeta mvs) = prettyM mvs <&> \doc -> "any(" <+> doc <+> ")"



