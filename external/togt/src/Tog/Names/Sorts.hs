{-# LANGUAGE NoImplicitPrelude #-}
module Tog.Names.Sorts
  (NameS, QNameS, Sorted(..), NameSort(..)
  ,DefNameSort(..), ConNameSort(..)
  ,IsQName(..)
   -- * Misc
  ,ProjName, pattern ProjNameS
   -- * Definitions
  ,DefSorted(..), IsDefName(..), DefName
  ,pattern DefNameS
  ,FDefName,  pattern FDefName
  ,PDefName,  pattern PDefName
  ,ConSorted(..), ConName, IsConName(..)
  ,pattern ConNameS
  ,TyConName, pattern TyConName --,TConNameSort(..)
 -- ,TConSorted(..),  pattern TConName, IsTConName(..), TConName
  ,DConName,  pattern DConName
  ,RConName,  pattern RConName
  ,sTrustMe
  ) where

import Tog.Prelude
import Tog.Names
import qualified Tog.PrettyPrint as PP
import Control.Comonad

-- | Something which is just a QName, with perhaps some annotations which are uniquely
--   determined up to the signature.
--   (e.g. no terms or anything).
class (Eq a, Show a) => IsQName a where getQName :: a -> QName
instance IsQName QName where getQName = id
instance IsQName a => IsQName (Tagged k a) where getQName = getQName . unTagged

-- | Names with a phantom sort
data NameSort =
    FDefS  -- ^ Function
  | PDefS  -- ^ Postulate
  | DConS  -- ^ Data constructor
  | RConS  -- ^ Record constructor
  | TyConS -- ^ Type constructor
  | ProjS  -- ^ Projection
  | ModS   -- ^ Module
  deriving (Eq, Generic, Show)

instance Hashable NameSort where

type Sorted c = Tagged (c :: NameSort)
type NameS c  = Sorted c Name
type QNameS c = Sorted c QName

sTrustMe :: forall c a. a -> Sorted c a 
sTrustMe = Tagged

type    ProjName  = QNameS 'ProjS
pattern ProjNameS :: a -> Sorted 'ProjS a
pattern ProjNameS x = Tagged x

pattern ConNameS :: ConNameSort c -> a -> ConSorted a
pattern ConNameS x y = ConName x (Tagged y)

type    DConName  = QNameS 'DConS
pattern DConName :: Sorted 'DConS a -> ConSorted a
pattern DConName x = ConName SDConS x
instance IsConName DConName where
  conName = ConName SDConS
  viewConName (ConName SDConS x) = Just x
  viewConName _                  = Nothing

type    RConName  = QNameS 'RConS
pattern RConName :: Sorted 'RConS a -> ConSorted a
pattern RConName x = ConName SRConS x
instance IsConName RConName where
  conName = ConName SRConS
  viewConName (ConName SRConS x) = Just x
  viewConName _                  = Nothing

-- * Sorts for constructors (that is, injective constants)
data ConNameSort (c :: NameSort) where
  SDConS  :: ConNameSort 'DConS
  SRConS  :: ConNameSort 'RConS
data ConSorted a where ConName :: forall s a. ConNameSort s -> Sorted s a -> ConSorted a 
deriving instance Show a => Show (ConSorted a)
deriving instance Functor ConSorted
type ConName = ConSorted QName

instance Comonad ConSorted where
  extract (ConName _ (Tagged a)) = a
  duplicate cn@(ConName sort _) = fmap (ConName sort . Tagged) cn

instance HasSrcLoc a => HasSrcLoc (ConSorted a) where
  srcLoc = srcLoc . extract

instance IsConName ConName where conName = id ; viewConName = Just
class IsQName a => IsConName a where
  conName     :: a -> ConName
  viewConName :: ConName -> Maybe a

instance Eq a => Eq (ConSorted a) where
  ConName _ (Tagged y1) == ConName _ (Tagged y2) = y1 == y2
instance PP.Pretty a => PP.Pretty (ConSorted a) where 
  pretty (ConName _ a) = PP.pretty a
instance NFData ConName where
  rnf = rnf . getQName


instance Hashable ConName where
  hashWithSalt i = hashWithSalt i . getQName

instance IsQName ConName where getQName (ConName _ n) = getQName n

deriving instance Eq (ConNameSort c)
deriving instance Show (ConNameSort c)

-- -- * Sorts for term constructors (either record, or data-type constructors)
-- data TConNameSort (c :: NameSort) where
--   TDConS  :: TConNameSort 'DConS
--   TRConS  :: TConNameSort 'RConS
-- data TConSorted a where TConSorted :: forall s a. TConNameSort s -> Sorted s a -> TConSorted a
-- type TConName = TConSorted QName
-- deriving instance Functor TConSorted
-- 
-- instance IsQName TConName where getQName (TConSorted _ name) = getQName name
-- instance Eq a => Eq (TConSorted a) where TConSorted _ (Tagged x) == TConSorted _ (Tagged y) = x == y
-- 
-- instance IsConName TConName where
--   conName (TConSorted TDConS q) = ConName SDConS q
--   conName (TConSorted TRConS q) = ConName SRConS q
--   viewConName :: ConName -> Maybe TConName
--   viewConName (ConName SDConS q)  = Just (TConSorted TDConS q)
--   viewConName (ConName SRConS q)  = Just (TConSorted TRConS q)
--   viewConName (ConName STyConS _) = Nothing
-- 
-- class IsConName a => IsTConName a where
--   tConName     :: a -> TConName
--   viewTConName :: TConName -> Maybe a
-- instance IsTConName TConName where tConName = id ; viewTConName = Just
-- instance IsTConName DConName where
--   tConName = TConSorted TDConS
--   viewTConName (TConSorted TDConS x) = Just x
--   viewTConName _ = Nothing
-- 
-- instance IsTConName RConName where
--   tConName = TConSorted TRConS
--   viewTConName (TConSorted TRConS x) = Just x
--   viewTConName _ = Nothing
-- 
-- pattern TConName :: TConName -> ConName                         
-- pattern TConName x <- (viewConName -> Just x)
--   where TConName x = conName x
-- 
-- * Definitions with phantom sort
data DefNameSort (c :: NameSort) where
  SFDefS  :: DefNameSort 'FDefS
  SPDefS  :: DefNameSort 'PDefS
  STyConS :: DefNameSort 'TyConS

deriving instance Eq (DefNameSort c)
deriving instance Show (DefNameSort c)

pattern DefNameS :: DefNameSort c -> a -> DefSorted a
pattern DefNameS x y = DefName x (Tagged y)

data DefSorted a where DefName :: forall s a. DefNameSort s -> Sorted s a -> DefSorted a
deriving instance Show a => Show (DefSorted a)
deriving instance Functor DefSorted
type DefName = DefSorted QName
class IsQName a => IsDefName a where
  defName :: a -> DefName
  viewDefName :: DefName -> Maybe a
instance IsDefName DefName where defName = id; viewDefName = Just

instance Comonad DefSorted where
  extract (DefName _ (Tagged a)) = a
  duplicate cn@(DefName sort _) = fmap (DefName sort . Tagged) cn

instance HasSrcLoc a => HasSrcLoc (DefSorted a) where
  srcLoc = srcLoc . extract

instance Eq a => Eq (DefSorted a) where
  DefName _ (Tagged y1) == DefName _ (Tagged y2) = y1 == y2

instance PP.Pretty a => PP.Pretty (DefSorted a) where 
  pretty (DefName _ a) = PP.pretty a

{-# COMPLETE PDefName, FDefName, TyConName #-}
type    PDefName  = QNameS 'PDefS
pattern PDefName :: Sorted 'PDefS a -> DefSorted a
pattern PDefName x = DefName SPDefS x               
instance IsDefName PDefName where
  defName = PDefName
  viewDefName (PDefName x) = Just x
  viewDefName _            = Nothing

type    FDefName =  QNameS 'FDefS
pattern FDefName :: Sorted 'FDefS a -> DefSorted a
pattern FDefName x = DefName SFDefS x               
instance IsDefName FDefName where
  defName = FDefName
  viewDefName (FDefName x) = Just x
  viewDefName _            = Nothing

type    TyConName  = QNameS 'TyConS
pattern TyConName :: Sorted 'TyConS a -> DefSorted a
pattern TyConName x = DefName STyConS x
instance IsDefName TyConName where
  defName = DefName STyConS
  viewDefName (DefName STyConS x) = Just x
  viewDefName _                   = Nothing

instance IsQName DefName where getQName = getDefQName

getDefQName :: DefName -> QName
getDefQName (DefName _ (Tagged n)) = n

-- Alternatively, we could just compare the QName and ignore the sorts
-- completely.
instance NFData DefName where rnf = rnf . getDefQName

instance Hashable DefName where
  hashWithSalt i = hashWithSalt i . getDefQName 
