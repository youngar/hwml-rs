{-# LANGUAGE NoImplicitPrelude #-}
module Tog.Elaborate.Constraint where

import Tog.Prelude
import Tog.Term
import Tog.Names

import           Tog.PrettyPrint                  (($$), (//>))
import qualified Tog.PrettyPrint                  as PP

-- Constraints
--------------

type Constraints t = Seq (Constraint t)

data Constraint t
  = JmEq SrcLoc
         (Ctx t)
         (Type t :∋ Term t)
         (Type t :∋ Term t)

instance PrettyM t (Constraint t) where
  prettyM c = case c of
    JmEq loc ctx (type1 :∋ t1) (type2 :∋ t2) -> localCtx ctx $ do
      locDoc <- pure$ PP.pretty loc
      ctxDoc <- prettyM ctx
      type1Doc <- prettyM type1
      t1Doc <- prettyM t1
      type2Doc <- prettyM type2
      t2Doc <- prettyM t2
      return $
        "JmEq" $$
        "loc:" //> locDoc $$
        "ctx:" //> ctxDoc $$
        "t:" //> t1Doc $$
        "A:" //> type1Doc $$
        "u:" //> t2Doc $$
        "B:" //> type2Doc

instance HasSrcLoc (Constraint t) where
  srcLoc (JmEq loc _ _ _) = loc
