module Tog.Unify.Impl.Mock ( Mock ) where

import Tog.Term (IsTerm, PrettyM(..))
import Tog.Unify.Class

data Mock 
instance UnifierImpl Mock where
  unifierShortName = "M"
  unifierLongName = "Mock"

instance IsTerm t => Unifier Mock t where
  data Constraint Mock t = Can'tSolve

  makeConstraint _ _ _ = newBlockedConstraint Bottom Can'tSolve
  refine _ = newBlockedConstraint Bottom Can'tSolve

instance PrettyM t (Constraint Mock t) where
  prettyM _p = pure "⊥"

instance ExpandGuards (Constraint Mock t) where
  expandGuards = pure
