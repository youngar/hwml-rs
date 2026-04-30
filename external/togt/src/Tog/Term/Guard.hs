module Tog.Term.Guard
       ( Guard
       , Guarded(..)
       , unguarded
       , unguarded'
       , unguardedInspect
       , qNameGuard
       , metaGuard
       , metasGuard
       , guardIsEmpty
       , openedQNameGuard
       , metasOnly
       , guardIsInstantiated
       )
       where

import Tog.Term.Core
import Tog.Names
import Tog.Names.Sorts (IsQName(..))
import qualified Data.ISet as I
import Control.Lens ((<&>))

import Algebra.Lattice hiding (join, meet)

data Guarded b = Guarded {
   
   guardian :: !Guard
 , guardedValue :: b
 }

guardIsInstantiated :: (MonadTerm t m) => Guard -> m Bool
guardIsInstantiated Guard{..} = do
  sig <- askSignature
--  (||) <$> (any (sigMetaIsInstantiated sig) <$> I.toList guardMetas) 
--       <*> (any (not . sigIsOpenDefinition sig) <$> I.toList guardOpenDefs)
  return$ sigMetasAreInstantiated sig guardMetas || sigDefinitionsAreInstantiated sig guardOpenDefs

unguarded :: (MonadTerm t m) => Guarded b -> m (Maybe b)
unguarded g = unguarded' g <&> \case
  Left{}  -> Nothing
  Right b -> Just b

unguarded' :: (MonadTerm t m) => Guarded b -> m (Either b b)
unguarded' Guarded{guardian,guardedValue} = do
  guardIsInstantiated guardian >>= \case
    True  -> return$ Left guardedValue
    False -> return$ Right guardedValue

unguardedInspect :: (MonadTerm t m) => Guarded b -> m (Either b (b, Guard))
unguardedInspect Guarded{guardian,guardedValue} = do
  guardIsInstantiated guardian >>= \case
    True  -> return$ Left guardedValue
    False -> return$ Right (guardedValue,guardian)
