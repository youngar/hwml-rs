module Tog.Instrumentation.Debug.Label (DebugLabel(..), debugLabelToString, debugLabelFromString) where

import Tog.Prelude
import Tog.PrettyPrint
import Data.Char
import Data.String.Utils (strip)

data DebugLabel =
    AddMeta
  | AddModule
  | AdLibitum
  | ApplyInvertMetaSubst
  | Audit
  | Check
  | CheckClause
  | CheckDecl
  | CheckEqualBlockedOn
  | CheckEqualSpine
  | CheckExpr
  | CheckMetaConsistency
  | CheckModule
  | CheckPhysEq
  | CheckSynEq
  | CheckSynEqExtra
  | Conversion
  | Compare
  | CurryMeta
  | DefEqual
  | Elaborate
  | Elaborate_constraint
  | ElaborateApp
  | ElaborateCon
  | EtaContract
  | EtaExpand
  | EtaExpandContextVar
  | EtaExpandMeta
  | Exec_EqualCanonical
  | Exec_EqualSpine
  | Exec_EqualTerm
  | Exec_InstantiateMeta
  | FreeVars
  | Infer
  | Instantiate
  | IsVarNotFree
  | InstantiateMeta
  | IntersectMetaSpine
  | InvertMeta
  | MaybeNf
  | MetaAssign
  | Metas
  | Metas_shallow
  | Meta_constraint
  | NewConstraint
  | Occurs
  | Occurs_shallow
  | PruneMeta
  | PruneTerm
  | RemoveProjections
  | Solve
  | Status
  | Twins
  | Unify
  | UnrollPi
  deriving (Eq, Ord, Show, Read, Enum, Bounded, Generic)

instance Hashable DebugLabel

-- | It holds that   debugLabelFromString . debugLabelToString  ==  Just
debugLabelToString :: DebugLabel -> String
debugLabelToString lbl =
  let c:cs = show lbl in
  toLower c : flip map cs (\case
                '_' -> '.'
                c'  -> c' )

debugLabelFromString :: String -> Maybe DebugLabel
debugLabelFromString str = do
  c:cs <- pure $ strip str
  let str' = toUpper c : flip map cs (\case
                '.' -> '_'
                c'  -> c' )
  readMaybe str'

instance Pretty DebugLabel where
  pretty = text . debugLabelToString
