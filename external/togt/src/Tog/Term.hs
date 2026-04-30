{-# LANGUAGE NoImplicitPrelude #-}
-- | Terms and a lot of facilities.  Output of typechecking.
module Tog.Term
  ( module Tog.Term.Types
    -- * Useful synonyms
  , module Tog.Term.Synonyms
    -- * Free variables
  , module Tog.Term.FreeVars
--    -- * 'IsTerm' implementations
--  , module Tog.Term.Impl
    -- * Folding over the `Meta`s in a term
  , module Tog.Term.MetaVars
  , MonadTerm
  , IsTerm
  , checkMetaOccurs
  ) where

import Tog.Prelude
import Tog.Term.Types hiding (IsTerm, MonadTerm)
import qualified Tog.Term.Types as T
import Tog.Term.Synonyms
import Tog.Term.Impl.Common (IsTermE(..))
import Tog.Term.MetaVars
import Tog.Term.FreeVars

import Tog.PrettyPrint ((//>), ($$))
import Tog.Monad (TC)

import Tog.Instrumentation.Debug
import qualified Tog.Instrumentation.Debug.Label as DL

type IsTerm = IsTermE
type MonadTerm t m = (IsTermE t, T.MonadTerm t m)

{-# SPECIALIZE checkMetaOccurs :: (IsTermE t) => Meta -> MetaBody t -> TC t r s (DoesNotOccur, MetaBody t) #-}
checkMetaOccurs :: (MonadTerm t m, Metas t a, Nf t a, PrettyM t a) => Meta -> a -> m (DoesNotOccur, a)
checkMetaOccurs mv t =
        let msg = do
                tDoc <- prettyM_ t
                mvDoc <- prettyM_ mv
                return$ 
                  "mv:" //> mvDoc $$
                  "t:" //> tDoc
        in
        debugBracket DL.Occurs msg $
        runFoldMetas (fmap Any . metaOccurs mv) t >>= \case
           Any False -> return (DoesNotOccur, t)
           Any True  -> do
             debug_ "" "normalizing during occurs check"
             t' <- maybeNf t
             Meet gs <- runFoldMetas (fmap Meet . metaOccursWhnf mv) t'
             return (gs,t')
