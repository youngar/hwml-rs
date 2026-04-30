{-# LANGUAGE NoImplicitPrelude #-}
module Tog.Term.Subst (SubstV(..)
                      ,pattern Id
                      ,pattern Weaken
                      ,pattern Strengthen
                      ,pattern Instantiate
                      ,pattern (:#)
                      ,pattern Lift
                      ,IsSubst(..)
                      ,GenericSubst
                      ,HasSubst(..)) where

import           Tog.Prelude
import           Tog.Term.Synonyms

-- | A substitution σ : Δ → Γ can be seen as a list of terms Γ ⊢ vᵢ : Aᵢ
--   with Aᵢ from Δ, that can be applied to a term Δ ⊢ u : B yielding
--   Γ ⊢ uσ : Bσ by substituting the vs for the variables in u.
--
--   In other
--   words, if  Γ ⊢ σ : Δ  then applySubst σ : Term Δ -> Term Γ.
data SubstV t σ
  = Id_
    --
    -- --------------------------------
    --   Γ ⊢ Id : Γ

  | Weaken_ !Natural σ
    --   Γ ⊢ σ : Δ
    -- --------------------------------
    --   Γ;Ψ ⊢ Weaken |Ψ| σ : Δ

  | Strengthen_ !Natural σ
    --   Γ ⊢ σ : Δ
    -- --------------------------------
    --   Γ ⊢ Strengthen |Ψ| σ : Δ; Ψ

  | Instantiate_ (Term t) σ
    --   Γ ⊢ u : Aσ    Γ ⊢ σ : Δ      Δ ⊢ A type
    -- ----------------------------------------------
    --   Γ ⊢ σ :# u : Δ; A

  | Lift_ !Natural σ
    --         Γ ⊢ σ : Δ       
    -- --------------------------------
    --    Γ;Ψσ ⊢ Lift |Ψ| σ : Δ;Ψ

  deriving (Eq, Show, Read, Generic)

instance (Hashable t, Hashable σ) => Hashable (SubstV t σ)

class IsSubst t σ | σ -> t where
  viewSub   :: σ -> SubstV t σ
  unviewSub :: SubstV t σ -> σ

pattern Id :: IsSubst t σ => σ
pattern Weaken :: IsSubst t σ => Natural -> σ -> σ
pattern Strengthen :: IsSubst t σ => Natural -> σ -> σ
pattern Instantiate :: IsSubst t σ => Term t -> σ -> σ
pattern Lift :: IsSubst t σ => Natural -> σ -> σ
pattern (:#) :: IsSubst t σ => σ -> Term t -> σ

pattern Id <- (viewSub -> Id_)
  where Id =   unviewSub$ Id_

pattern Weaken n σ <- (viewSub -> Weaken_ n σ)
  where Weaken n σ =   unviewSub$ Weaken_ n σ

pattern Strengthen n σ <- (viewSub -> Strengthen_ n σ)
  where Strengthen n σ =   unviewSub$ Strengthen_ n σ

pattern Instantiate σ t <- (viewSub -> Instantiate_ σ t)
  where Instantiate σ t =   unviewSub$ Instantiate_ σ t

pattern Lift n σ <- (viewSub -> Lift_ n σ)
  where Lift n σ =   unviewSub$ Lift_ n σ

pattern σ :# t = Instantiate t σ

newtype GenericSubst t = GS { unGS :: SubstV t (GenericSubst t) }
                         deriving (Eq, Hashable)

{-# COMPLETE Id, Weaken, Strengthen, Instantiate, Lift :: GenericSubst #-}
{-# COMPLETE Id, Weaken, Strengthen, (:#), Lift :: GenericSubst #-}
-- Note that, for GenericSubst, `viewSub` and `unviewSub` are compiled
-- to identity functions.
instance IsSubst t (GenericSubst t) where                         
  viewSub = unGS
  unviewSub = GS

-- Try reenable in GHC 8.4
{- COMPLETE Id, Weaken, Strengthen, Instantiate, Lift :: Subst -}
{- COMPLETE Id, Weaken, Strengthen, (:#), Lift :: Subst -}
class IsSubst t (Subst t) => HasSubst t where
  data Subst t
