{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS -fno-warn-orphans #-}
module Tog.Term.Core
  ( -- * Var
    Var
  , unVar
  , mkVar
  , varIndex
  , boundVar
  , weakenVar
  , weakenVar_
  , strengthenVar
  , strengthenVar_
  , VarSet
  , weakenVars_
  , strengthenVars_
  , HasVar(varP)
  , atDir
    -- * Free variables
  , DoesNotOccur, pattern DoesNotOccur, pattern Rigidly, pattern Flexibly 
  , flexibleUnder
  , FreeVars(..)
  , FreeVarSet(..)
  , MonadFreeVars
    -- * Named
  , named
  , Named(..)
  , NoNames, runNoNames
    -- * Terms
  , TermView(..)
  , Projection(..)
  , Head(..)
  , headIsNeutral
  , isHeadVar
  , inferHeadType
  , Opened, pattern Opened, opndKey, opndArgs
  , pattern OTyCon, pattern OFDef, pattern OPDef, pattern ORCon, pattern ODCon
  , ForAllQName
  , Elim(..), Elims
  , isApply
  , isProj
  , Field(..)
  , Abs(..)
  , pattern Abs_
    -- * Term typeclasses
  , Term₀(..)
    -- ** Metas
  , MetaSet
  , QNameSet
  , Metas(..)
  , Meta(..)
    -- ** Nf
  , Nf(..)
    -- ** ExpandMetas
  , ExpandMetas(..), runExpandMetas, evalExpandMetas
    -- ** Pretty
  , NamesT
  , runNamesT
  , MonadNames(..)
  , localAddNames
  , PrettyM(..)
  , prettyMWithCtx, prettyM_
  , prettyPrecMWithCtx, prettyPrecM_
  , PrettyMWrapper(..)
  , PrettyWrapper(..)
    -- ** Subst
  , ApplySubstM
  , runSafeApplySubst
  , ApplySubst(..)
  , TraverseOpen(..)
  , OpenTerm(..)
    -- ** SynEq
  , SynEq(..)
    -- * IsTerm
  , IsTerm(..)
  , HasSubst(..)
  , whnfView
  , BlockedTerm(..)
  , ignoreMetaBlocking
  , ignoreMetaBlocking_
  , ignoreBlockedOn
  , noMemoize
  , MemoizeCache(..)
    -- ** Blocked
  , Blocked(..)
  , BlockedHead(..)
  , MetaBlocked(..)
    -- ** Guards
  , Guard(..)
  , GuardLattice
  , qNameGuard
  , metaGuard
  , metasGuard
  , guardIsEmpty
  , openedQNameGuard
  , metasOnly
    -- ** Smart constructors
  , var
  , lam, lam_
  , pi, pi_
  , equal
  , app
  , def
  , meta
  , con
  , twin
  , var_
    -- * Definition
  , Contextual(..)
  , openContextual
  , openContextualAbstract
  , ignoreContextual
  , Module
  , ContextualDef
  , Definition(..)
  , openDefinition
  , Constant(..)
  , FunInst(..)
  , ClauseBody(..)
  , Clause(..)
  , Pattern(..)
  , patternBindings
  , patternsBindings
  , Invertible(..)
  , TermHead(..)
  , ignoreInvertible
  , definitionType
  , sigIsOpenDefinition
    -- * MonadTerm
  , MonadTerm(..)
  , MonadUnview
  , UnsafeTermM
  , runUnsafeTermM
  , TermM
  , TermMF(..)
  , runTermM
  , getDefinition
  , getMaxClauseArity
  , getMetaType
  , lookupMetaBody
    -- * Signature
  , MetaBody(..)
  , metaBodyToTerm
    -- | Signature is an ADT, so invariants can be preserved.
  , Signature
  , sigEmpty
  , askSignatureMixin
  , withSignatureMixin
    -- ** Querying
  , sigGetDefinition
  , sigLookupDefinition
  , sigGetMetaType
  , sigLookupMetaBody
  , sigDefinedNames
  , sigDefinedMetas
  , sigMetaIsInstantiated
  , sigMetasAreInstantiated
  , sigDefinitionsAreInstantiated
  , sigUninstantiatedMetas
  , sigInstantiatedMetas
  , sigDefinedMetaMaxBound
    -- ** Updating
  , sigAddPostulate
  , sigAddData
  , sigAddRecordCon
  , sigAddRecordConSignature
  , sigAddTypeSig
  , sigAddClauses
  , sigAddProjection
  , sigAddDataCon
  , sigAddModule
  , sigAddMeta
  , sigInstantiateMeta
  --   -- ** Utils
  -- , sigToScope
    -- * Context
  , Dir(..)
  , CtxType(..)
  , Ctx(..), ICtx
  , Ctx_, ICtx_, Tel_
  , ctxSingleton
  , ctxLength
  , ctxWeaken
  , ctxWeaken_
  , ctxLookupName
  , ctxLookupNameIdx
  , ctxLookupVar
  , ctxGetVar
  , ctxVars
  , ctxIndexed
  , ctxUnindex
  , ctxPi
  , ctxLam
  , ctxApp
    -- * Telescope
  , Tel(..)
  , ctxToTel
  , telToCtx
  , telLength
  , telAppend
  , telDischarge
  , telPi
  , telVars
  , telApp
    -- ** Smart constructors
  , subId
  , subSingleton
  , subWeaken
  , subInstantiate
  , subStrengthen
  , subLift
  , subFromList
    -- ** Operations
  , subChain
  , subCompose
  , subLookup
  , subLookupTwin
  , subNull
    -- ** Operations on terms
  , weaken
  , weaken_
  -- , strengthen
  -- , strengthen_
  , instantiate
  , instantiate_
  , getAbsName
  , getAbsName_
  , eliminate
    -- * Clauses invertibility
  , termHead
  , checkInvertibility
    -- * Subterms
  , HasSubterms(..)
    -- * Utilities
  , debugResult
  ) where

import           Control.Monad.Reader        (ReaderT, runReaderT, ask, local)
import           Control.Monad.State         (modify, get)
import           Control.Monad.Trans.Except (ExceptT)
import           Control.Monad.Trans.State.Strict  (StateT,  evalStateT)
import           Control.Monad.Trans.Writer.Strict (WriterT)
import           Control.Monad.Except              (throwError)

import qualified Data.HashSet                     as HS
import qualified Data.KHashMap                    as HMS
import           Data.List.NonEmpty               (NonEmpty(..))
import qualified Data.List.NonEmpty               as NE
import qualified Data.ISet                        as I
import qualified Data.BitSet                      as B
import           Data.PhysEq
import qualified Data.Semigroup                   as Sg
import           Data.FreeLattice

import           Tog.Instrumentation
import qualified Tog.Instrumentation.Debug.Label  as DL
import           Tog.Prelude
import           Tog.Names
import           Tog.Names.Sorts
import qualified Tog.PrettyPrint                  as PP
import           Tog.Term.Subst
import           Tog.Term.Synonyms
import           GHC.Magic  (inline)
import           Tog.PrettyPrint                  ((<+>), ($$), (</>), (//>), ($$>), (//))
import qualified Tog.Term.Subst                   as Sub
import           System.IO.Unsafe                 (unsafePerformIO)

import qualified Data.Kind as K


#include "impossible.h"

-- Var
------------------------------------------------------------------------

newtype Var = V {unVar :: Natural}
  deriving (Show, Eq, Ord, Hashable, Enum, NFData)

instance ISetMember Var where repr = fromIntegral . varIndex
type NoNames = Identity
runNoNames :: NoNames a -> a
runNoNames = runIdentity
instance ISetMemberM NoNames Var where full = pure . mkVar ("_" :: Name) . fromIntegral

type VarSet = BitSet Var

{-# INLINE mkVar #-}
mkVar :: Name -> Natural -> Var
mkVar _ i | i < 0 = error "impossible.mkVar"
mkVar _ i = V i 

varIndex :: Var -> Natural
varIndex = unVar

instance PP.Pretty Var where
  pretty v = PP.pretty (varIndex v) <> "#" <> PP.pretty ("_" :: Name)

boundVar :: Name -> Var
boundVar _ = V 0

weakenVar :: Natural -> Natural -> Var -> Var
weakenVar from by (V ix) =
  let ix' = if ix >= from
            then ix + by
            else ix
  in V ix'

weakenVar_ :: Natural -> Var -> Var
weakenVar_ = weakenVar 0

weakenVars_ :: Natural -> VarSet -> VarSet
weakenVars_ = B.integerAction . fromIntegral

strengthenVar :: Natural -> Natural -> Var -> Maybe Var
strengthenVar from by (V ix) =
  let ix' | ix < from      = Just ix
          | ix < from + by = Nothing
          | otherwise      = Just $ ix - by
  in V <$> ix'

strengthenVar_ :: Natural -> Var -> Maybe Var
strengthenVar_ = strengthenVar 0

strengthenVars_ :: Natural -> VarSet -> VarSet
strengthenVars_ = B.integerAction . negate . fromIntegral

-- Named
------------------------------------------------------------------------

named :: Name -> a -> Named a
named = Named

data Named a = Named
  { namedName :: !Name
  , unNamed   :: !a
  } deriving (Show, Functor, Foldable, Traversable)

instance Eq a => Eq (Named a) where
  Named _ v1 == Named _ v2 = v1 == v2

instance Ord a => Ord (Named a) where
  Named _ v1 `compare` Named _ v2 = v1 `compare` v2

instance (Hashable a) => Hashable (Named a) where
  hashWithSalt s = hashWithSalt s . unNamed

instance Enum a => Enum (Named a) where
  fromEnum (Named _ v) = fromEnum v
  toEnum   a           = Named mempty (toEnum a)

instance NFData a => NFData (Named a) where
  rnf a = rnf (namedName a) `seq` rnf (unNamed a) `seq` ()

instance PP.Pretty a => PP.Pretty (Named a) where
  pretty Named{namedName, unNamed} = PP.pretty namedName <+> ":" <+> PP.pretty unNamed

-- Record 'Field's
------------------------------------------------------------------------

-- | The field of a projection.
newtype Field = Field {unField :: Natural}
    deriving (Eq, Ord, Show, Hashable, NFData)

-- Terms
------------------------------------------------------------------------

data Dir = Fst | Snd deriving (Show, Eq, Generic, Enum)

instance Hashable Dir
instance NFData Dir

instance PP.Pretty Dir where
  pretty Fst = "´"
  pretty Snd = "`"

-- | A 'Head' heads a neutral term -- something which can't reduce
-- further.
--
-- This is not exactly true; a term headed by a Def could reduce
-- by δ-expansion.
data Head t
    = Var !Var
    | Twin !Dir !Var -- | Represents a twin variable
    | Def {-# UNPACK #-} !(Opened DefName t)
    | Meta {-# UNPACK #-} !Meta
    | J
    deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

-- | Checks if a head is a variable.
--   Note that directionality is forgoten.
isHeadVar :: Head t -> Maybe Var
isHeadVar (Var v)      = Just v
isHeadVar (Twin _d v)  = Just v 
isHeadVar Def{}        = Nothing
isHeadVar Meta{}       = Nothing
isHeadVar J{}          = Nothing

-- | Infers the type of a neutral term
inferHeadType
  :: MonadTerm t m
  => Ctx t -> Head t -> m (Type t)
inferHeadType ctx h = case h of
  Var v    -> ctxGetVar v ctx
  Twin _ _ -> __IMPOSSIBLE__
  Def name -> definitionType =<< getDefinition name
  Meta mv  -> getMetaType mv
  J        -> return typeOfJ

-- | Check whether a Head is stuck forever
headIsNeutral :: MonadTerm t m => Head t -> m Bool
headIsNeutral = \case
  (Def f) -> do
    def' <- getDefinition f
    case def' of
      Constant _ Function{}  -> return False
      
      -- We need to check whether a function is stuck on a variable
      -- (not meta variable), but the API does not help us...
      Constant _ Data{}      -> return True
      Constant _ Record{}    -> return True
      Constant _ Postulate{} -> return True
      _                     -> __IMPOSSIBLE__
  Var{}  -> return True
  Twin{} -> return True
  Meta{} -> return False
  J{} -> 
    return False
  
instance (Hashable t) => Hashable (Head t)
instance (NFData t) => NFData (Head t)

data Opened key t = Opened_
  { opndKey  :: !key
  , opndArgs :: ![Term t]
    -- ^ The arguments of the contexts the definition corresponding to
    -- 'DefKey' is in.  They must match the length of the telescope in
    -- 'Contextual'.
  } deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

{-# COMPLETE Opened #-}
pattern Opened :: t -> [Term a] -> Opened t a
pattern Opened k as <- Opened_ k as
  where Opened k as = seqList as $ Opened_ k as

{-# INLINE viewOConName #-}
viewOConName :: forall a t. IsConName a => Opened ConName t -> Maybe (Opened a t)
viewOConName (Opened (viewConName -> Just name) args) = Just (Opened name args)
viewOConName _ = Nothing

{-# COMPLETE ODCon, ORCon #-}
pattern ODCon :: Opened DConName t -> Opened ConName t                       
pattern ODCon x <- (viewOConName -> Just x)
  where ODCon (Opened dConName args) = Opened (conName dConName) args
pattern ORCon :: Opened RConName t -> Opened ConName t                       
pattern ORCon x <- (viewOConName -> Just x)
  where ORCon (Opened dConName args) = Opened (conName dConName) args

{-# INLINE viewODefName #-}
viewODefName :: Opened DefName t -> Either (Opened FDefName t)
                                           (Either (Opened PDefName t)
                                                   (Opened TyConName t))
viewODefName (Opened (FDefName name) args) = Left (Opened name args)
viewODefName (Opened (PDefName name) args) = Right (Left (Opened name args))
viewODefName (Opened (TyConName name) args) = Right (Right (Opened name args))

{-# COMPLETE OTyCon, OFDef, OPDef #-}
pattern OTyCon :: Opened TyConName t -> Opened DefName t                       
pattern OTyCon x <- (viewODefName -> Right (Right x))
  where OTyCon (Opened dDefName args) = Opened (defName dDefName) args
pattern OFDef :: Opened FDefName t -> Opened DefName t                       
pattern OFDef x <- (viewODefName -> Left x)
  where OFDef (Opened dDefName args) = Opened (FDefName dDefName) args
pattern OPDef :: Opened PDefName t -> Opened DefName t                       
pattern OPDef x <- (viewODefName -> Right (Left x))
  where OPDef (Opened dDefName args) = Opened (PDefName dDefName) args

sOTrustMe :: forall s a. Opened QName a -> Opened (QNameS s) a
sOTrustMe = coerce

------------------------------------------------------------------------------

instance (Hashable key, Hashable t) => Hashable (Opened key t)
instance (NFData key, NFData t) => NFData (Opened key t)

instance Bifunctor Opened where
  bimap f g (Opened k args) = Opened (f k) (fmap g args)

-- | 'Elim's are applied to 'Head's.  They're either arguments applied
-- to functions, or projections applied to records.
data Elim t
  = Apply !t
  | Proj !Projection
  deriving (Eq, Show, Generic, Functor, Foldable, Traversable)

-- ^ Elims are applied from left to right
type Elims t = [Elim t]

instance (Hashable t) => Hashable (Elim t)
instance (NFData t) => NFData (Elim t)

isApply :: Elim (Term t) -> Maybe (Term t)
isApply (Apply v) = Just v
isApply Proj{}    = Nothing

isProj :: Elim (Term t) -> Maybe Projection
isProj Apply{}  = Nothing
isProj (Proj p) = Just p

data Projection = Projection'
  { pName  :: !ProjName
  , pField :: !Field
  } deriving (Show, Eq, Ord, Generic)

instance Hashable Projection
instance NFData Projection
instance SynEq t Projection where synEq = (pure .).(==)

instance PP.Pretty Projection where
  pretty = PP.pretty . pName

-- | The 'TermView' lets us pattern match on terms.  The actual
-- implementation of terms might be different, but we must be able to
-- get a 'TermView' out of it.  See 'View'.


#if TogLazyTermView
-- | `Abs` is something with a free `0` variable
data Abs a = Abs { absName :: Name, unAbs :: a } deriving (Eq, Show, Functor, Generic)
data TermView t
    = Pi (Type t) (Abs (Type t))
    | Lam (Abs t)
    | Equal (Type t) (Term t) (Term t)
    | Refl
    | Set
    | Con (Opened ConName t) [Term t]
    | App (Head t) [Elim t]
    deriving (Eq, Generic, Show, Functor, Foldable, Traversable)
#elif TogStrictTermView
data Abs a = Abs { absName :: Name, unAbs :: !a } deriving (Eq, Show, Functor, Generic)
data TermView t
    = Pi !(Type t) !(Abs (Type t))
    | Lam !(Abs t)
    | Equal !(Type t) !(Term t) !(Term t)
    | Refl
    | Set
    | Con !(Opened ConName t) [Term t]
    | App !(Head t) [Elim t]
    deriving (Eq, Generic, Show, Functor, Foldable, Traversable)
#endif

-- | Names with a phantom sort
{-# COMPLETE Abs_ #-}
pattern Abs_ :: a -> Abs a 
pattern Abs_ a <-  Abs _ a 
  where Abs_ a =   Abs "_" a

deriving instance Foldable Abs
deriving instance Traversable Abs

instance Hashable t => Hashable (Abs t)
instance NFData   t => NFData (Abs t)

instance (Hashable t) => Hashable (TermView t)
instance (NFData t) => NFData (TermView t)

-- Term typeclasses
------------------------------------------------------------------------

-- Metas
-----------
{-
-- Operations that can be run on the metavariables of a term
-- By giving explicit constructors for some of them, they can be
-- memoized.
data MetasProgram u where
  Generic        :: (forall m u. (Monad m, MonoidM u) => Meta -> m u) -> MetasProgram u
  OccursShallow  :: Meta        -> MetasProgram Any
  OccursDeep     :: Meta        -> MetasProgram Any
  MetaSetShallow ::                MetasProgram (ISet Meta)
  MetaSetDeep    ::                MetasProgram (ISet Meta)

yieldMeta :: (Monad m, MonoidM u, MonadReader (MetasProgram u) m) => Meta -> m u
yieldMeta mv = ask >>= flip go mv
  where
    go :: forall m u. (Monad m, MonoidM u) => MetasProgram u -> Meta -> m u
    go (Generic f) mv  = f mv
    go (OccursShallow mv') mv = if mv == mv' then return$ Any True else return$ Any False 
    go (OccursDeep mv')    mv = if mv == mv' then return$ Any True else return$ Any False 
    go (MetaSetShallow)    mv = return$ I.singleton mv 
    go (MetaSetDeep)       mv = return$ I.singleton mv 

instance MonadVisit m => MonadVisit (ReaderT a m) where
  visitQName q m = do
    env <- ask
    lift$ visitQName q (runReaderT m env)

  visitMeta mv m = do
    env <- ask
    lift$ visitMeta mv (runReaderT m env)
-}
type MetaSet = ISet Meta
type QNameSet = ISet QName

newtype Term₀ t = Term { getTerm  :: t }

class Metas t a where
  -- | Calls the function for the terms where one would reasonably expect to find metas
  foldMetas :: (Monad m, MonoidM u) => a -> ReaderT (t -> m u) m u

deriving instance Metas t a => Metas t (Tagged c a)

-- Guards
------------------------------------------------------------------------
data Guard = Guard {
   guardMetas    :: !(ISet Meta)
   -- | In tog, all the clauses for a function are added atomically.
   --   If that was not the case, we would store a map  QName -> Int instead,
   --   so that we can detect if there are extra definitions we want to
   --   look at.                     
 , guardOpenDefs :: !(ISet QName)
 } deriving (Show, Eq, Generic, Ord) 

instance        JoinSemiLattice Guard where (Guard a b) \/ (Guard a' b')
                                              = Guard (a <> a') (b <> b')
instance BoundedJoinSemiLattice Guard where bottom = Guard mempty mempty

instance Sg.Semigroup Guard where                
  (<>) = (\/)

instance Monoid Guard where             
  mempty = bottom
  mappend = (\/) 

type GuardLattice = FreeLattice Guard
instance FreeLatticeBase Guard where simpleJoin = inj . mconcat

instance PrettyM t GuardLattice where
  prettyPrecM = prettyPrecFLM prettyPrecM

{-# INLINE qNameGuard #-}
qNameGuard :: IsQName qname => qname -> Guard
qNameGuard qname = bottom{guardOpenDefs = I.singleton$ getQName qname}

openedQNameGuard :: IsQName qname => Opened qname t -> Guard
openedQNameGuard (Opened qname _) = qNameGuard qname

metaGuard :: Meta -> Guard 
metaGuard mv = bottom{guardMetas = I.singleton mv}

metasGuard :: MetaSet -> Guard
metasGuard mvs = bottom{guardMetas = mvs}

guardIsEmpty :: Guard -> Bool
guardIsEmpty (Guard guardMetas guardOpenDefs) = I.null guardMetas && I.null guardOpenDefs

metasOnly :: Guard -> Guard
metasOnly gs = Guard{guardMetas = guardMetas gs,guardOpenDefs = mempty} 

-- Nf
------------------------------------------------------------------------

class Nf t a where
  nf :: (MonadTerm t m) => a -> m a

instance Nf t (Elim t) where
  nf (Proj p)  = return $ Proj p
  nf (Apply t) = Apply <$> nf t

instance Nf t a => Nf t (Abs a) where
  nf (Abs name a) = Abs name <$> nf a

instance Nf t a => Nf t [a] where
  nf = mapM nf

instance Nf t a => Nf t (Maybe a) where
  nf = traverse nf

instance (Nf t a, Nf t b) => Nf t (a, b) where
  nf (a,b) = (,) <$> nf a <*> nf b

instance (Nf t a, Nf t b) => Nf t (a :∈ b) where
  nf (a :∈ b) = (:∈) <$> nf a <*> nf b

instance Nf t a => Nf t (NonEmpty a) where
  nf = mapM nf

-- Meta instantiation
------------------------------------------------------------------------

class ExpandMetas t a where
  -- | This function instantiates all the metas in a term(-container),
  --   and returns i) which metas could not be instantiated, and ii)
  --   which definitions were found in the term.
  --
  --   This can double up as a cheap occurs check before
  --   actually normalizing.
  expandMetas :: (MonadTerm t m) => a -> WriterT Guard m a

instance ExpandMetas t (Elim t) where
  expandMetas (Proj p)  = return $ Proj p
  expandMetas (Apply t) = Apply <$> expandMetas t

instance ExpandMetas t a => ExpandMetas t (Abs a) where
  expandMetas (Abs name a) = Abs name <$> expandMetas a

instance ExpandMetas t a => ExpandMetas t [a] where
  expandMetas = mapM expandMetas

instance ExpandMetas t a => ExpandMetas t (Maybe a) where
  expandMetas = traverse expandMetas

instance (ExpandMetas t a, ExpandMetas t b) => ExpandMetas t (a, b) where
  expandMetas (a,b) = (,) <$> expandMetas a <*> expandMetas b

instance (ExpandMetas t a, ExpandMetas t b) => ExpandMetas t (a :∈ b) where
  expandMetas (a :∈ b) = (:∈) <$> expandMetas a <*> expandMetas b

instance ExpandMetas t a => ExpandMetas t (NonEmpty a) where
  expandMetas = mapM expandMetas

runExpandMetas :: (ExpandMetas t a, MonadTerm t m) => a -> m (a, Guard)
runExpandMetas = expandMetas >>> runWriterT

evalExpandMetas :: (ExpandMetas t a, MonadTerm t m) => a -> m a
evalExpandMetas = expandMetas >>> evalWriterT


-- Pretty
------------------------------------------------------------------------

-- Local names for prettyprinting

class Monad m => MonadNames m where
  -- | Names a variable
  varName :: Var -> m Name

  -- | Adds a name to the pretty-printing context
  localAddName :: Name -> m a -> m a 

  -- | Replaces the pretty-printing context 
  localCtx :: Ctx b -> m a -> m a 

  -- | Variables a name (may fail)
  lookupCtxName :: Name -> m Var

localAddNames :: MonadNames m => [Name] -> m a -> m a
localAddNames [] m = m
localAddNames (n:ns) m = localAddName n$ localAddNames ns m

newtype NamesT m a = NamesT { unNamesT :: ReaderT (Ctx ()) m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadConf)

deriving instance (MonadTerm t m) => MonadTerm t (NamesT m)

instance Monad m => MonadNames (NamesT m) where
  localAddName name = NamesT . local (:< (name, ())) . unNamesT
  varName v = NamesT$ ask <&> fromMaybe "_" . ctxNameVar v
  localCtx ctx = NamesT . local (const (fmap (const ()) ctx)) . unNamesT
  lookupCtxName name = NamesT ask <&> ctxLookupNameIdx name >>= \case
              Just v   -> return v
              Nothing  -> NamesT ask >>= \ctx -> fail$ "Variable " <> show name <> " not in context " <> show ctx 

runNamesT :: Ctx b -> NamesT m a -> m a
runNamesT ctx = flip runReaderT (fmap (const ()) ctx) . unNamesT

class PrettyM t a where
  {-# MINIMAL prettyPrecM | prettyM #-}

  prettyPrecM :: (MonadTerm t m, MonadNames m) => Int -> a -> m PP.Doc
  prettyPrecM _ = prettyM

  prettyM :: (MonadTerm t m, MonadNames m) => a -> m PP.Doc
  prettyM = prettyPrecM 0

deriving instance PrettyM t a => PrettyM t (Tagged c a)

data PrettyMWrapper t where
  PrettyM :: PrettyM t a => a -> PrettyMWrapper t

newtype PrettyWrapper a = Pretty a

prettyPrecMWithCtx :: (MonadTerm t m, PrettyM t a) => Ctx u -> Int -> a -> m PP.Doc
prettyPrecMWithCtx ctx p = runNamesT ctx . prettyPrecM p

prettyMWithCtx :: (MonadTerm t m, PrettyM t a) => Ctx u -> a -> m PP.Doc
prettyMWithCtx ctx = runNamesT ctx . prettyM

prettyPrecM_ :: (MonadTerm t m, PrettyM t a) => Int -> a -> m PP.Doc
prettyPrecM_ = prettyPrecMWithCtx C0

prettyM_ :: forall t m a. (MonadTerm t m, PrettyM t a) => a -> m PP.Doc
prettyM_ = prettyMWithCtx C0

instance PP.Pretty a => PrettyM t (PrettyWrapper a) where
  prettyM (Pretty  a) = pure$ PP.pretty a
  prettyPrecM n (Pretty  a) = pure$ PP.prettyPrec n a

instance PrettyM t (PrettyMWrapper t) where                           
  prettyM (PrettyM a) = prettyM a
  prettyPrecM n (PrettyM a) = prettyPrecM n a

instance PrettyM t a => PrettyM t (Elim a) where
  prettyPrecM p (Apply t) = do
    tDoc <- prettyPrecM p t
    return $ PP.condParens (p > 0) $ "$" <+> tDoc
  prettyPrecM _ (Proj p) = do
    -- Hacky
    let t = pName p
    tDoc <- prettyM t
    let pDoc = tDoc
    return $ "." <> pDoc

instance PrettyM t a => PrettyM t (Abs a) where
  prettyPrecM p (Abs name t) = localAddName name $ prettyPrecM p t
  prettyM (Abs name t) = localAddName name $ prettyM t

instance PrettyM t a => PrettyM t [a] where
  prettyM x = PP.list <$> mapM prettyM x

instance PrettyM t a => PrettyM t (Seq a) where
  prettyM x = PP.list <$> mapM prettyM (toList x)

instance (PP.Pretty key, PrettyM t a) => PrettyM t (Opened key a) where
  prettyM (Opened key []) = return$ PP.pretty key
  prettyM (Opened key args) = do
    argsDoc <- prettyM args
    return$ PP.pretty key <> "@" <> argsDoc

instance PrettyM t Var where 
  prettyM v = do
    n <- varName v
    return$ PP.pretty (varIndex v) <> "#" <> PP.pretty n

instance PrettyM t a => PrettyM t (NonEmpty a) where
  prettyM x = PP.list <$> mapM prettyM (NE.toList x)

instance (PrettyM t a, ISetMemberTermM a) => PrettyM t (ISet a) where
  prettyPrecM prec t = iSetMemberTermM t >>= \Dict -> I.toList t >>= prettyPrecM prec

instance PrettyM t a => PrettyM t (TermView a) where
  prettyPrecM p e =
    case e of
      Lam (Abs name body) -> do
        bodyP <- localAddName name (prettyM body)
        return$
          PP.condParens (p > 0) $
            "λ" <+> PP.pretty name <> "." <+> bodyP

      Pi dom (Abs name cod) -> do
        domP <- prettyM dom
        codP <- localAddName name (prettyM cod) 
        return$
          PP.condParens (p > 0) $ PP.align $
            "(" <+> PP.pretty name <+> ":" <+> domP <+> ")" // codP

      Equal a x y -> do
        prettyAppM p (PP.text "_==_") [a, x, y]

      Refl ->
        return $ PP.text "refl"

      Con dataCon args -> do
        cP <- prettyPrecM p dataCon 
        prettyAppM p cP args

      Set ->
        return $ PP.text "Set"

      App h args -> do
        hP <- prettyPrecM p h
        args1 <- case h of
          Var{} ->
            return ([])
          Twin{} ->
            return ([])
          Def (Opened _f args') ->
            return$ map Apply args'
          Meta _mv ->
            return []
          J ->
            return []
        prettyAppM p hP (args1 ++ args)

   where
     prettyAppM :: forall a m. (MonadTerm t m, MonadNames m, PrettyM t a) => Int -> PP.Doc -> [a] -> m PP.Doc
     prettyAppM _ h []   = return h
     prettyAppM p h args0 = do
       argsP <- prettyArgs (reverse args0)
       return$ PP.condParens (p > 3) $ h <> PP.nest 2 (PP.group argsP)
       where
         prettyArgs []           = return PP.empty
         prettyArgs [arg]        = (PP.line <>) <$> prettyPrecM 4 arg
         prettyArgs (arg : args) = do
           argP <- prettyPrecM 4 arg
           argsP <- prettyArgs args
           return$ PP.group argsP $$ argP




   
  

-- Subst
------------------------------------------------------------------------

type ApplySubstM = ExceptT Var

runSafeApplySubst :: ApplySubstM m a -> m (Either Var a)
runSafeApplySubst = runExceptT

data TraverseEnv t m = TraverseEnv {
   traverseLift :: forall a. Nat -> m a -> m a
  ,traverseTerm :: t -> m t
  }

class TraverseOpen t a | a -> t where
  traverseOpen :: (Applicative m) => a
                                  -> TraverseEnv t m
                                  -> m a

newtype OpenTerm t = OpenTerm { unOpenTerm :: t }
deriving instance PrettyM t t => PrettyM t (OpenTerm t)

instance ApplySubst t t => ApplySubst t (OpenTerm t) where
instance TraverseOpen t (OpenTerm t) where
  traverseOpen (OpenTerm t) TraverseEnv{traverseTerm} = OpenTerm <$> traverseTerm t 

class ApplySubst t a | a -> t where
  safeApplySubst :: (MonadTerm t m) => a -> Subst t -> ApplySubstM m a
  default safeApplySubst :: (TraverseOpen t a, MonadTerm t m) => a -> Subst t -> ApplySubstM m a
  safeApplySubst a rho = flip runReaderT rho $ traverseOpen a
    TraverseEnv{traverseLift = local . subLift
               ,traverseTerm = \t -> ask >>= lift . safeApplySubst t
               }

  applySubst :: (MonadTerm t m) => a -> Subst t -> m a
  default applySubst :: (TraverseOpen t a, MonadTerm t m) => a -> Subst t -> m a
  applySubst a rho = flip runReaderT rho $ traverseOpen a
    TraverseEnv{traverseLift = local . subLift
               ,traverseTerm = \t -> ask >>= lift . applySubst t
               }

  safeStrengthen :: (MonadTerm t m) => a -> Var -> m (Maybe a)
  default safeStrengthen :: (TraverseOpen t a, MonadTerm t m) => a -> Var -> m (Maybe a)
  safeStrengthen a var = runMaybeT$ flip runReaderT var $ traverseOpen a
    TraverseEnv{traverseLift = local . weakenVar_
               ,traverseTerm = \t -> ask >>= lift . MaybeT . safeStrengthen t
               }
instance ApplySubst t a => ApplySubst t (Tagged c a) where
  safeApplySubst (Tagged a) σ = coerce <$> safeApplySubst a σ
  applySubst     (Tagged a) σ = coerce <$> applySubst a σ
  safeStrengthen (Tagged a) v = coerce <$> safeStrengthen a v

instance TraverseOpen t a => TraverseOpen t (Tagged c a) where
  traverseOpen   (Tagged a) env = coerce <$> traverseOpen a env

instance ApplySubst t (Elim t)
instance TraverseOpen t (Elim t) where
  traverseOpen (Proj p)  _   = pure $ Proj p
  traverseOpen (Apply t) TraverseEnv{traverseTerm} = Apply <$> traverseTerm t

instance (TraverseOpen t a) => ApplySubst t [a]
instance TraverseOpen t a => TraverseOpen t [a] where
  traverseOpen t rho = traverse (`traverseOpen` rho) t

instance ApplySubst t (Clause t)
instance TraverseOpen t (Clause t) where
  traverseOpen (Clause pats t) rho@TraverseEnv{traverseLift} =
    Clause pats <$> traverseLift (patternsBindings pats) (traverseOpen t rho)

instance ApplySubst t (ClauseBody t) where
instance TraverseOpen t (ClauseBody t) where
  traverseOpen cb TraverseEnv{traverseTerm} = case cb of
    ClauseNoBody -> pure ClauseNoBody
    ClauseBody t -> ClauseBody <$> traverseTerm t

instance ApplySubst t (Definition Const t) where
instance TraverseOpen t (Definition Const t) where
  traverseOpen (Constant type_ constant) rho@TraverseEnv{traverseTerm} =
    Constant <$> traverseTerm type_ <*> traverseOpen constant rho
  traverseOpen (DataCon tyCon args dataConType) rho =
    DataCon tyCon args . coerce <$> traverseOpen (coerce dataConType :: Contextual t (OpenTerm t)) rho
  traverseOpen (Projection fld tyCon projType) rho =
    Projection fld tyCon . coerce <$> traverseOpen (coerce projType :: Contextual t (OpenTerm t)) rho
  traverseOpen (Module (Contextual tel names)) rho =
    Module <$> (Contextual . coerce <$> traverseOpen (coerce tel :: Tel (OpenTerm t)) rho <*> pure names)

instance ApplySubst t (Constant Const t) where
instance TraverseOpen t (Constant Const t) where
  traverseOpen Postulate _ = do
    pure Postulate
  traverseOpen (Data dataCons) _ = do
    pure $ Data dataCons
  traverseOpen (Record dataCon projs) _ = do
    pure $ Record dataCon projs
  traverseOpen (Function inst) rho = do
    Function <$> traverseOpen inst rho

instance ApplySubst t (FunInst t) where
instance TraverseOpen t (FunInst t) where
  traverseOpen Open       _   = pure Open
  traverseOpen (Inst inv) rho = Inst <$> traverseOpen inv rho

instance ApplySubst t (Invertible t) where
instance TraverseOpen t (Invertible t) where
  traverseOpen (NotInvertible clauses) rho = do
    NotInvertible <$> traverseOpen clauses rho
  traverseOpen (Invertible clauses) rho = do
    Invertible <$> (flip traverse clauses $ \(th, clause) -> (th,) <$> traverseOpen clause rho)

instance (TraverseOpen t a, ApplySubst t a) => ApplySubst t (Contextual t a) where
instance (TraverseOpen t a) => TraverseOpen t (Contextual t a) where
  traverseOpen (Contextual tel x) rho@TraverseEnv{traverseLift} =
    Contextual <$> (coerce <$> traverseOpen (coerce tel :: Tel (OpenTerm t)) rho)
               <*> traverseLift (telLength tel) (traverseOpen x rho)

instance (TraverseOpen t a, ApplySubst t a) => ApplySubst t (Opened key a) where
instance (TraverseOpen t a) => TraverseOpen t (Opened key a) where
  traverseOpen (Opened n args) rho = Opened n <$> traverseOpen args rho

instance (TraverseOpen t a, TraverseOpen t b, ApplySubst t a, ApplySubst t b) => ApplySubst t (a :∈ b) where
instance (TraverseOpen t a, TraverseOpen t b) => TraverseOpen t (a :∈ b) where
  traverseOpen (a :∈ b) σ = (:∈) <$> traverseOpen a σ <*> traverseOpen b σ

-- SynEq
------------------------------------------------------------------------

class SynEq t a where
  synEq :: (MonadTerm t m) => a -> a -> m Bool

deriving instance SynEq t a => SynEq t (Tagged c a)

instance SynEq t a => SynEq t (Abs a) where
  synEq = synEq `on` unAbs

instance SynEq t (Elim t) where
  synEq e1 e2 = case (e1, e2) of
    (Proj p1,  Proj p2)  -> synEq p1 p2
    (Apply t1, Apply t2) -> synEq t1 t2
    (_,        _)        -> return False

instance SynEq t (Blocked t) where
  synEq blockedX blockedY = case (blockedX, blockedY) of
    (NotBlocked x, NotBlocked y) ->
      synEq x y
    (BlockingHeadMeta mv1 els1, BlockingHeadMeta mv2 els2) | mv1 == mv2 ->
      synEq els1 els2
    (BlockingHeadDef key1 els1, BlockingHeadDef key2 els2) ->
      andM [synEq key1 key2, synEq els1 els2]
    (BlockedOn mvs1 f1 els1, BlockedOn mvs2 f2 els2) | mvs1 == mvs2 ->
      synEq (f1, els1) (f2, els2)
    (_, _) ->
      return False

instance SynEq t a => SynEq t [a] where
  synEq []       []       = return True
  synEq (x : xs) (y : ys) = synEq (x, xs) (y, ys)
  synEq _        _        = return False

instance SynEq t a => SynEq t (NonEmpty a) where
  synEq (a :| as) (b :| bs) = synEq (a,as) (b,bs)

instance (SynEq t a, SynEq t b) => SynEq t (a, b) where
  synEq (x1, y1) (x2, y2) = do
    b <- synEq x1 x2
    if b then synEq y1 y2 else return False

instance (SynEq t a, SynEq t b, SynEq t c) => SynEq t (a, b, c) where
  synEq (x1, y1, z1) (x2, y2, z2) = do
    b1 <- synEq x1 x2
    if b1
      then do
        b2 <- synEq y1 y2
        if b2 then synEq z1 z2 else return False
      else return False

instance (Eq key) => SynEq t (Opened key t) where
  synEq (Opened k1 args1) (Opened k2 args2) =
    if k1 == k2
      then synEq args1 args2
      else return False

instance SynEq t (BlockedHead t) where
  synEq (BlockedOnFunction f1) (BlockedOnFunction f2) =
    synEq f1 f2
  synEq BlockedOnJ BlockedOnJ =
    return True
  synEq _ _ =
    return False

instance SynEq t (Head t) where
  synEq (Var v1) (Var v2) =
    return $ v1 == v2
  synEq (Def dk1) (Def dk2) =
    synEq dk1 dk2
  synEq J J =
    return True
  synEq (Meta mv1) (Meta mv2) =
    return $ mv1 == mv2
  synEq _ _ =
    return False

-- | Functions on terms
newtype TermMF t a b = TermMF { termMF :: forall m. MonadTerm t m => a -> m b }

type MonadUnview t m = ({- MonadIO m, -} Monad m, IsTerm t)

-- IsTerm
------------------------------------------------------------------------

type MonadFreeVars t m = (MonadTerm t m)

----- Blocking of terms
class BlockedTerm t a | a -> t where
  ignoreBlocking  :: MonadTerm t m => a -> m t 
  ignoreBlocking  = unview <=< ignoreBlocking_
  ignoreBlocking_ :: MonadTerm t m => a -> m (TermView t)
  ignoreBlocking_ = view <=< ignoreBlocking
  isBlocked       :: a -> Maybe Guard

instance BlockedTerm t (MetaBlocked t) where
  isBlocked = isMetaBlocked
  ignoreBlocking = ignoreMetaBlocking_
  ignoreBlocking_ = ignoreMetaBlocking

ignoreMetaBlocking :: MonadUnview t m => MetaBlocked t -> m (TermView t) 
ignoreMetaBlocking = \case
    MetaNotBlocked t       -> view t
    MetaBlockingHead mv es -> pure$ App (Meta mv) es

ignoreMetaBlocking_ :: MonadUnview t m => MetaBlocked t -> m t 
ignoreMetaBlocking_ = \case
    MetaNotBlocked t       -> pure t
    MetaBlockingHead mv es -> meta mv es

isMetaBlocked :: MetaBlocked t -> Maybe Guard
isMetaBlocked (MetaNotBlocked{}) = Nothing
isMetaBlocked (MetaBlockingHead mv _) = Just (metaGuard mv)

instance BlockedTerm t (Blocked t) where
  ignoreBlocking :: (MonadTerm t m) => Blocked t -> m t
  ignoreBlocking (NotBlocked t) = return t
  ignoreBlocking (BlockingHeadMeta mv es) = meta mv es
  ignoreBlocking (BlockingHeadDef  key es) = def key es
  ignoreBlocking (BlockedOn _ bh es) = ignoreBlockedOn bh es

  ignoreBlocking_ (NotBlocked t) = view t
  ignoreBlocking_ (BlockingHeadMeta mv es) = pure$ App (Meta mv) es
  ignoreBlocking_ (BlockingHeadDef  key es) = pure$ App (Def key) es
  ignoreBlocking_ (BlockedOn _ bh es) = pure$ ignoreBlockedOn_ bh es

  isBlocked :: Blocked t -> Maybe Guard
  isBlocked (NotBlocked _)      = Nothing
  isBlocked (BlockingHeadMeta mv _) = Just $ metaGuard mv
  isBlocked (BlockingHeadDef  (Opened key _) _) = Just$ qNameGuard $ getQName key
  isBlocked (BlockedOn mvs _ _) = Just mvs

type MonadFreeVars' t m = MonadTerm t m

class (Typeable t, Show t, Nf t t, PrettyM t t, ApplySubst t t, SynEq t t, PhysEq t,
       ExpandMetas t t,
       DefaultM IO (SignatureMixin t), HasSubst t, FreeVars t t, Monoid (Taint t)) => IsTerm t where

    shortName :: String
    longName  :: String

    -- Evaluation (βηδ-reduction)
    --------------------------------------------------------------------
    whnf :: MonadTerm t m => Term t -> m (Blocked (Term t))
    whnfMeta :: MonadTerm t m => Term t -> m (MetaBlocked (Term t))
    viewW :: MonadTerm t m => t -> m (TermView t) 
    viewW = whnfMeta >=> ignoreMetaBlocking 
    whnfMetaTerm :: MonadTerm t m => t -> m t
    whnfMetaTerm = whnfMeta >=> ignoreMetaBlocking_

    -- View / Unview
    --------------------------------------------------------------------

    -- | Note that nobody outside @Term/@ should use 'view' -- and in fact
    -- it's not exported from 'Term'.  Why?  Because you always want
    -- 'whnfView', that is a view with respect to the current signature.
    --
    -- However, if you are traversing a whole term for a substitution-like
    -- operation that does not affect closed terms, then using `view` is
    -- legitimate.
    view    :: MonadUnview t m => Term t -> m (TermView t)

    -- | Similarly, nobody outside @Term/@ should use 'unview', but only
    -- the "smart constructors" below.  Why?  Resilience to future
    -- changes and more importantly we make lists of eliminators strict
    -- in the smart constructors.
    unview  :: MonadUnview t m => TermView t -> m (Term t)

    -- We require these to be un-monadic mostly because having them
    -- monadic is a huge PITA when writing the type-checker/unifier.
    -- And, for 'typeOfJ', for performance reasons.
    set     :: Closed (Term t)
    refl    :: Closed (Term t)
    typeOfJ :: Closed (Type t)


    -- Performance enhancements
    -----------------------------

    -- | Some representations might want to do this more efficiently
    whnfTerm :: (MonadTerm t m) => Term t -> m (Term t)
    whnfTerm = ignoreBlocking <=< whnf

    -- | We make wrap the result in `m` to help with type inference.
    termIsHashable :: MonadTerm t m => m (Maybe (Dict (Eq t, Hashable t)))
    termIsHashable = return Nothing

    -- | Term representations may access and update this mixin
    type SignatureMixin (t :: TypeK) :: TypeK
    type SignatureMixin t = ()

    -- | Memoize functions in the Monad
    memoize :: (MonadTerm t m) => MemoizeCache t a b -> (a -> m (b,Taint t)) -> (a -> m b)
    memoize = noMemoize

    --  Tools for memoization
    ----------------------------
    type Taint (t :: TypeK) :: TypeK
    type Taint t = ()

    taint   :: (MonadTerm t m) => Taint t -> m ()
    taint _ = return ()

    taintDefinition :: (MonadTerm t m) => QName -> m ()
    taintDefinition _ = taint mempty

    inspect :: (MonadTerm t m) => m a -> m (a, Taint t)
    inspect = fmap (,mempty)

    scrub   :: (MonadTerm t m) => m a -> m a
    scrub   = id

    --  Tools for initialization and cleanup
    -------------------------------------------
    termReprInitialize :: (MonadTerm t m) => m ()
    termReprFinalize   :: (MonadTerm t m) => m ()
    termReprInitialize = return ()
    termReprFinalize   = return ()

    -- Meta variables
    --------------------
    {- -- | Generic function for metavariable traversals
    foldMetas :: (MonadTerm  t m,
                  MonadVisit m,
                  MonoidM    u) => a -> ReaderT (MetasProgram u) m u
    -}

whnfView :: (MonadTerm t m) => Term t -> m (TermView t)
whnfView = whnfTerm >=> view

noMemoize :: (MonadTerm t m) => MemoizeCache t a b -> (a -> m (b, Taint t)) -> (a -> m b)
noMemoize _ = (fmap fst .)  

-- | Memoization is limited to a few predetermined functions.
--   This introduces coupling between the implementation of the term
--   and the functions that are memoized. On the other hand, this allows
--   each term implementation to memoize each type of information as it sees
--   fit (e.g. HashTable, Tree, other).
data MemoizeCache t a b where
  EtaExpandMetaCache  :: MemoizeCache t (Type t) (Maybe (MetaBody t, Term t))
  EtaExpandCache      :: MemoizeCache t (Type t :∋ Term t) (Term t)
  UnrollPiCache       :: MemoizeCache t (Type t) (Tel (Type t), Type t)

-- | Representation of blocked terms.  Right now we just use 'Meta', but
-- in the future we want to support unistantiated functions too (see
-- Issue 5).
data Blocked t
  = NotBlocked t
  | BlockingHeadMeta Meta [Elim t]
  | BlockingHeadDef  (Opened DefName t) [Elim t]
  -- ^ The term is headed byj some blocking thing.
  | BlockedOn Guard  (BlockedHead t) [Elim t]
  -- ^ Some meta-variables are preventing us from reducing a definition.  The
  -- 'BlockedHead' is the head, the 'Elim's the eliminators stuck on it.
  --
  -- Note that the metavariables impeding reduction might be both at
  -- the head of some eliminators, or impeding reduction of some other
  -- definition heading an eliminator.  In other words, even if the
  -- term is blocked, we don't guarantee that every eliminator is
  -- constructor headed.
  deriving (Eq, Show, Typeable, Functor)

-- | Analogous of `Blocked` for `whnfMeta`
data MetaBlocked t
  = MetaNotBlocked t
    -- ^ Term not headed by a meta
  | MetaBlockingHead Meta [Elim t]
    -- ^ Headed by blocking meta
  deriving (Eq, Show, Typeable, Functor)

data BlockedHead t
    = BlockedOnFunction !(Opened DefName t)
    | BlockedOnJ
    deriving (Eq, Show, Typeable, Functor)

ignoreBlockedOn :: (MonadTerm t m) => BlockedHead t -> [Elim t] -> m t
ignoreBlockedOn bh es =
  let h = case bh of
            BlockedOnFunction fun -> Def fun
            BlockedOnJ            -> J
  in app h es

ignoreBlockedOn_ :: BlockedHead t -> [Elim t] -> TermView t
ignoreBlockedOn_ bh es =
  let h = case bh of
            BlockedOnFunction fun -> Def fun
            BlockedOnJ            -> J
  in App h es

-- Term utils
-------------

seqList :: [a] -> b -> b
seqList []        x = x
seqList (!_ : xs) y = seqList xs y

var :: (MonadUnview t m) => Var -> m t
var v = app (Var v) []

lam :: (MonadUnview t m) => Abs t -> m t
lam body = unview $ Lam body

lam_ :: (MonadUnview t m) => t -> m t
lam_ = lam . Abs_

pi :: (MonadUnview t m) => t -> Abs t -> m t
pi domain codomain = unview $ Pi domain codomain

pi_ :: (MonadUnview t m) => t -> t -> m t
pi_ domain = pi domain . Abs_

equal :: (MonadUnview t m) => t -> t -> t -> m t
equal type_ x y = unview $ Equal type_ x y

app :: (MonadUnview t m) => Head t -> [Elim t] -> m t
app h elims = seqList elims $ unview $ App h elims

meta :: (MonadUnview t m) => Meta -> [Elim t] -> m t
meta mv elims  = seqList elims $ app (Meta mv) elims

def :: (IsDefName defName, MonadUnview t m) => Opened defName t -> [Elim t] -> m t
def f elims = seqList elims $ app (Def (first defName f)) elims

con :: (IsConName conName, MonadUnview t m) => Opened conName t -> [Term t] -> m t
con c args = seqList args $ unview $ Con (first conName c) args

twin :: (MonadUnview t m) => Dir -> Var -> m t
twin dir v = app (Twin dir v) []

var_ :: forall t m. (MonadUnview t m) => Maybe Dir -> Var -> m t
var_ Nothing = var
var_ (Just dir) = twin dir

-- Clauses
------------------------------------------------------------------------

-- | A 'ClauseBody' scopes a term over a number of variables.  The
-- lowest number refers to the rightmost variable in the patterns, the
-- highest to the leftmost.
--
-- If we have an empty pattern, we're not going to have a clause body.
data ClauseBody t
  = ClauseBody (Term t)
  | ClauseNoBody
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

-- | One clause of a function definition.
data Clause t = Clause [Pattern t] (ClauseBody t)
    deriving (Eq, Show, Typeable, Functor)

data Pattern t
    = VarP
    | ConP (Opened DConName t) [Pattern t]
    | EmptyP
    deriving (Eq, Show, Typeable, Functor)

patternBindings :: Pattern t -> Natural
patternBindings VarP          = 1
patternBindings (ConP _ pats) = patternsBindings pats
patternBindings EmptyP        = 0

patternsBindings :: [Pattern t] -> Natural
patternsBindings = sum . map patternBindings

-- Definition
------------------------------------------------------------------------

data Contextual t a = Contextual
  { contextualTelescope :: !(Tel t)
  , contextualInside    :: !a
  } deriving (Eq, Show, Typeable)

instance Bifunctor Contextual where
  bimap f g (Contextual tel t) = Contextual (fmap f tel) (g t)


openContextual
  :: (ApplySubst t a, PrettyM t a, MonadTerm t m, IsTerm t) => Contextual t a -> [Term t] -> m a
openContextual (Contextual tel a) args = do
  if telLength tel /= length args
    then __IMPOSSIBLE__
    else instantiate a args

openContextualAbstract :: Monad m => Natural -> Contextual t a -> m a
openContextualAbstract n (Contextual tel a)  = do
  if telLength tel /= n
    then __IMPOSSIBLE__
    else return a

ignoreContextual :: Contextual t a -> a
ignoreContextual (Contextual _ x) = x

type ContextualDef t = Contextual t (Definition Const t)

-- | A module, containing some names.  Note that once we reach
-- type-checking every name is fully qualified, so modules at these
-- stage are only opened so that we can instantiate their arguments.
type Module t = Contextual t (HS.HashSet QName)

data Definition f t
  = Constant (Type t) (Constant f t)
  | DataCon (f TyConName t) Natural (Contextual t (Type t))
  -- ^ Data type name, number of arguments, telescope ranging over the
  -- parameters of the type constructor ending with the type of the
  -- constructor.
  | Projection Field (f TyConName t) (Contextual t (Type t))
  -- ^ Field number, record type name, telescope ranging over the
  -- parameters of the type constructor ending with the type of the
  -- projected thing and finally the type of the projection.
  | Module (Module t)

deriving instance (Eq (Constant f t), ForAllQName Eq f t, Eq t) => Eq (Definition f t)
deriving instance (Show (Constant f t), ForAllQName Show f t, Show t) => Show (Definition f t)

openDefinition
  :: forall t m. (MonadTerm t m, IsTerm t)
  => ContextualDef t -> [Term t] -> m (Definition Opened t)
openDefinition ctxt args = do
  def' <- openContextual ctxt args
  return $ case def' of
    Constant type_ constant -> Constant type_ $ openConstant constant
    DataCon dataCon args' type_ -> DataCon (openName dataCon) args' type_
    Projection fld tyCon type_ -> Projection fld (openName tyCon) type_
    Module names -> Module names
  where
    openName :: Const a t -> Opened a t
    openName (Const n) = Opened n args

    openConstant Postulate = Postulate
    openConstant (Data dataCons) = Data $ map openName dataCons
    openConstant (Record dataCon projs) = Record (openName dataCon) (map openName projs)
    openConstant (Function inst) = Function inst

data Constant f t
  = Postulate
  -- ^ A postulate
  | Data ![f DConName t]
  -- ^ A data type, with constructors.
  | Record !(f RConName t) ![f Projection t]
  -- ^ A record, with its constructor and projections.
  | Function !(FunInst t)
  -- ^ A function, which might be waiting for instantiation
#if __GLASGOW_HASKELL__ >= 708
  deriving (Typeable)
#endif

type ForAllQName (c :: (K.Type -> K.Constraint)) f t =
  (c (f QName t), c (f DefName t), c (f ConName t),
   c (f DConName t), c (f RConName t),
   c (f TyConName t), c (f FDefName t), c (f PDefName t))

deriving instance (ForAllQName Eq f t, Eq (f Projection t), Eq t) => Eq (Constant f t)
deriving instance (ForAllQName Show f t, Show (f Projection t), Show t) => Show (Constant f t)

data FunInst t
  = Inst !(Invertible t)
  | Open
  deriving (Eq, Show, Typeable, Functor)

-- | A function is invertible if each of its clauses is headed by a
-- different 'TermHead'.
data Invertible t
  = NotInvertible [Clause t]
  | Invertible [(TermHead, Clause t)]
  -- ^ Each clause is paired with a 'TermHead' that doesn't happend
  -- anywhere else in the list.
  deriving (Eq, Show, Typeable, Functor)

-- | A 'TermHead' is an injective type- or data-former.
data TermHead
  = PiHead
  | DefHead QName
  deriving (Eq, Show)

instance PP.Pretty TermHead where
  pretty = PP.text . show

ignoreInvertible :: Invertible t -> [Clause t]
ignoreInvertible (NotInvertible clauses) = clauses
ignoreInvertible (Invertible injClauses) = map snd injClauses

definitionType :: (MonadTerm t m) => Closed (Definition n t) -> m (Closed (Type t))
definitionType (Constant type_ _) =
  return type_
definitionType (DataCon _ _ (Contextual tel type_)) =
  telPi tel type_
definitionType (Projection _ _ (Contextual tel type_)) =
  telPi tel type_
definitionType (Module _) =
  __IMPOSSIBLE__

-- 'Meta'iables
------------------------------------------------------------------------

-- | 'Meta'-variables.  Globally scoped.
--
--   Invariant: all values of type 'Meta' correspond to an existing
--   metavariable in a signature.
data Meta = MV
  { metaId     :: {-# UNPACK #-} !Int
  , metaSrcLoc :: SrcLoc
  } deriving (Show, Generic)

instance ISetMember Meta where repr = metaId

instance Eq Meta where
  (==) = (==) `on` metaId

instance Ord Meta where
  compare = comparing metaId

instance Hashable Meta where
  hashWithSalt s = hashWithSalt s . metaId

instance PP.Pretty Meta where
  prettyPrec _ (MV mv _) = PP.text $ "_" ++ show mv

instance PP.Pretty (PP.Verbose Meta) where
  prettyPrec _ (PP.Verbose (MV mv loc)) = "_" <> PP.text (show mv) <> "@" <> PP.pretty loc

instance PrettyM a Meta where
  prettyM = return . PP.pretty

instance HasSrcLoc Meta where
  srcLoc = metaSrcLoc

instance NFData Meta

-- MonadTerm
------------------------------------------------------------------------

----
class (Functor m, Applicative m, Monad m, MonadIO m, IsTerm t, MonadConf m) => MonadTerm t m | m -> t where
  askSignature :: m (Signature t)
  modifySignatureMixin :: (SignatureMixin t -> SignatureMixin t) -> m ()

newtype UnsafeTermM t a = UnsafeTermM { unUnsafeTermM :: a } deriving (Functor)

runUnsafeTermM :: forall t a. UnsafeTermM t a -> a
runUnsafeTermM = unUnsafeTermM

instance Applicative (UnsafeTermM t) where
  pure  = UnsafeTermM
  f <*> a = UnsafeTermM$ runUnsafeTermM f $ runUnsafeTermM a

instance Monad (UnsafeTermM t) where
  return = UnsafeTermM
  a >>= f  = UnsafeTermM$ runUnsafeTermM . f $ runUnsafeTermM a

instance IsTerm t => MonadTerm t (UnsafeTermM t) where
  askSignature = sigEmpty
  modifySignatureMixin _ = pure ()

instance MonadIO (UnsafeTermM t) where
  liftIO = UnsafeTermM . unsafePerformIO

instance MonadConf (UnsafeTermM t) where
  readConf = pure defaultConf
--------

newtype TermM t a = TermM (ReaderT Conf (StateT (Signature t) IO) a)
  deriving (Functor, Applicative, Monad, MonadIO)

instance (MonadConf (TermM t)) where
  readConf = TermM ask

instance (IsTerm t) => MonadTerm t (TermM t) where
  askSignature = TermM get
  modifySignatureMixin f = TermM $ modify $ withSignatureMixin f

instance (MonadTerm t m) => MonadTerm t (ExceptT a m) where
  askSignature = lift askSignature
  modifySignatureMixin = lift . modifySignatureMixin

instance (MonadTerm t m, Monoid a) => MonadTerm t (WriterT a m) where
  askSignature = lift askSignature
  modifySignatureMixin = lift . modifySignatureMixin

instance (MonadTerm t m) => MonadTerm t (ReaderT a m) where
  askSignature = lift askSignature
  modifySignatureMixin = lift . modifySignatureMixin

instance (MonadTerm t m) => MonadTerm t (StateT a m) where
  askSignature = lift askSignature
  modifySignatureMixin = lift . modifySignatureMixin

instance (MonadTerm t m) => MonadTerm t (MaybeT m) where
  askSignature = lift askSignature
  modifySignatureMixin = lift . modifySignatureMixin

askSignatureMixin :: (MonadTerm t m) => m (SignatureMixin t)
askSignatureMixin = sigMixin <$> askSignature

withSignatureMixin :: (SignatureMixin t -> SignatureMixin t) ->
                      (Signature      t -> Signature      t)
withSignatureMixin f = \sig@Signature{sigMixin} -> sig{sigMixin = f sigMixin}

runTermM :: Conf -> Signature t -> TermM t a -> IO a
runTermM conf sig (TermM m) = flip evalStateT sig $ flip runReaderT conf $ m

{-# INLINE getDefinition #-}
getDefinition :: forall t m qname. (MonadTerm t m, IsTerm t, IsQName qname) => Opened qname t -> m (Definition Opened t)
getDefinition n = do
  sig <- askSignature
  openDefinition (sigGetDefinition sig (getQName$ opndKey n)) (opndArgs n)

getMaxClauseArity :: (MonadTerm t m, IsTerm t) => Opened FDefName t -> m (Maybe Nat)
getMaxClauseArity f = do
  fDef <- getDefinition f
  case fDef of 
    Constant _ (Function (Inst (ignoreInvertible -> cs))) -> do
      return $ Just $ case cs of
        -- Assume that all clauses have the same arity
        (Clause ps _):_ -> length ps
        _    -> 0 
    _ -> return Nothing

getMetaType :: (MonadTerm t m) => Meta -> m (Type t)
getMetaType mv = (`sigGetMetaType` mv) <$> askSignature


lookupMetaBody :: (MonadTerm t m) => Meta -> m (Maybe (MetaBody t))
lookupMetaBody mv = (`sigLookupMetaBody` mv) <$> askSignature

-- getModule :: (MonadTerm t m) => QName -> m (Contextual t (HS.HashSet QName))
-- getModule n = (`sigGetModule` n) <$> askSignature

  

-- Signature
------------------------------------------------------------------------

data MetaBody t = MetaBody
  { mbArguments :: !Natural
    -- ^ The length of the context the meta lives in.
  , mbBody      :: !(Term t)
  } deriving (Eq, Show, Typeable, Generic)
instance (NFData t) => NFData (MetaBody t)
instance Nf a t => Nf a (MetaBody t) where
  nf (MetaBody a b) = MetaBody a <$> nf b
instance ExpandMetas a t => ExpandMetas a (MetaBody t) where
  expandMetas (MetaBody a b) = MetaBody a <$> expandMetas b
instance Hashable t => Hashable (MetaBody t)

-- | Invariant:  check C0 [ mvType ] [ metaBodyToTerm ] == True
metaBodyToTerm :: (MonadTerm t m) => MetaBody t -> m (Term t)
metaBodyToTerm (MetaBody args mvb) = go args
  where
    go 0 = return mvb
    go n = lam_ =<< go (n-1)

metaBodySpine :: forall t m. (MonadTerm t m) => MetaBody t -> m ([Elim t], Term t)
metaBodySpine (MetaBody args mvb) = sequence (go args) <&> (, mvb)
  where
    go :: Natural -> [m (Elim t)]
    go 0 = []
    go n = (Apply <$> var (mkVar "_" (n-1))):go (n-1)
 

-- | A 'Signature' stores every globally scoped thing.
--
--   We make the fields strict so that we do not keep hold of old Signatures
--   when updating them.
data Signature t = Signature
    { sigDefinitions      :: !(HMS.KHashMap QName (ContextualDef t))
    , sigMetasTypes       :: !(HMS.KHashMap Meta (Type t))
    , sigMetasBodies      :: !(HMS.KHashMap Meta (MetaBody t))

      -- | Invariant: if a meta is present in 'sigMetasBodies', it's in
      -- 'sigMetasTypes'.
    , sigMetasCount        :: {-# UNPACK #-} !Int

      -- | Term representations may include additional elements in the signature
      --   for book-keeping purposes.                            
    , sigMixin            :: !(SignatureMixin t)

      -- | Keep track of instantiated metavariables and bodies
    , sigMetasInstantiated        :: !(ISet Meta) 
    , sigDefinitionsInstantiated  :: !(ISet QName) 
    }

-- | Contract: If a function is defined for a signature `s`, it must be defined
--   and give the same result as for all signatures `s'`, if s and s' are related
--   under the reflexive, transitive closure of the relation R,  a R b iff
--   `(sigVersion b) = versionIncr (sigVersion a)`.
--   If a function fulfils this contract, then it can be safely memoized.

sigEmpty :: (MonadIO m, IsTerm t) => m (Signature t)
sigEmpty = do
  let sigDefinitions = HMS.empty
  let sigMetasTypes  = HMS.empty
  let sigMetasBodies = HMS.empty
  let sigMetasCount  = 0
  sigMixin <- liftIO defM
  let sigMetasInstantiated = mempty
  let sigDefinitionsInstantiated = mempty
  return Signature{..}

sigLookupDefinition :: IsQName qname => Signature t -> qname -> Maybe (ContextualDef t)
sigLookupDefinition sig key = HMS.lookupValue (getQName key) (sigDefinitions sig)

-- | Gets a definition for the given 'DefKey'.
sigGetDefinition :: IsQName qname => Signature t -> qname -> Closed (ContextualDef t)
sigGetDefinition sig key = case HMS.lookupValue (getQName key) (sigDefinitions sig) of
  Nothing   -> __IMPOSSIBLE__
  Just def' -> def'

-- Adding new definitions shouldn't change the result of previous “reductions”
-- (in the sense that calling sigAddDefinition if the definition exists 
-- already is __IMPOSSIBLE__).
sigAddDefinition :: IsQName qname => Signature t -> qname -> ContextualDef t -> Signature t
sigAddDefinition sig key def' = case sigLookupDefinition sig key of
  Nothing -> sigInsertDefinition sig key def'
  Just _  -> __IMPOSSIBLE__

sigInsertDefinition :: IsQName qname => Signature t -> qname -> ContextualDef t -> Signature t
sigInsertDefinition sig key def' =
  sig{sigDefinitions = HMS.insertValue (getQName key) def' $! sigDefinitions sig }

sigInstantiateDefinition :: IsQName qname => Signature t -> qname -> ContextualDef t -> Signature t
sigInstantiateDefinition sig key def' =
  sig{sigDefinitions = HMS.insertValue (getQName key) def' $! sigDefinitions sig
     ,sigDefinitionsInstantiated = I.insert (getQName key) $! sigDefinitionsInstantiated sig}

sigAddPostulate :: Signature t -> PDefName -> Tel t -> Type t -> Signature t
sigAddPostulate sig name tel type_ =
  sigInstantiateDefinition sig name $ Contextual tel $ Constant type_ Postulate

sigAddData :: Signature t -> TyConName  -> Tel t -> Type t -> Signature t
sigAddData sig name tel type_ =
  sigAddDefinition sig name $ Contextual tel $ Constant type_ $ Data []

sigAddRecordCon :: Signature t -> Opened TyConName t -> RConName -> Signature t
sigAddRecordCon sig name0 dataCon =
  case sigGetDefinition sig name of
    Contextual tel (Constant type_ (Function Open)) -> do
      sigInstantiateDefinition sig name $ Contextual tel $ Constant type_ $ Record (Const dataCon) []
    _ -> do
      __IMPOSSIBLE__
  where
    name = opndKey name0

sigAddTypeSig :: IsDefName defName => Signature t -> defName -> Tel t -> Type t -> Signature t
sigAddTypeSig sig name tel type_ =
  sigAddDefinition sig name $ Contextual tel $ Constant type_ $ Function Open

sigIsOpenDefinition :: Signature t -> QName -> Bool
sigIsOpenDefinition sig qname = case sigGetDefinition sig qname of
  Contextual _ (Constant _ (Function Open)) -> True
  _                                         -> False

-- | We take an 'Opened QName t' because if we're adding clauses the
-- function declaration must already be opened.
sigAddClauses :: Signature t -> Opened FDefName t -> Invertible t -> Signature t
sigAddClauses sig name0 clauses =
  let name = opndKey name0
      def' = case sigGetDefinition sig name of
        Contextual tel (Constant type_ (Function Open)) ->
          Contextual tel $ Constant type_ $ Function $ Inst clauses
        _ ->
          __IMPOSSIBLE__
  in sigInstantiateDefinition sig name def'

sigAddProjection
  :: Signature t -> ProjName -> Field -> Opened TyConName t -> Contextual t (Type t) -> Signature t
sigAddProjection sig0 projName projIx tyCon0 ctxtType =
  case sigGetDefinition sig0 tyCon of
    Contextual tel (Constant tyConType (Record dataCon projs)) ->
      let def' = Contextual tel $ Projection projIx (Const tyCon) ctxtType
          sig  = sigAddDefinition sig0 projName def'
          projs' = projs ++ [Const (Projection' projName projIx)]
      in sigInsertDefinition sig tyCon $
         Contextual tel $ Constant tyConType (Record dataCon projs')
    _ ->
      __IMPOSSIBLE__
  where
    tyCon = opndKey tyCon0

sigAddDataCon
  :: Signature t -> DConName -> Opened TyConName t -> Natural -> Contextual t (Type t) -> Signature t
sigAddDataCon sig0 dataConName tyCon0 numArgs ctxtType =
  case sigGetDefinition sig0 tyCon of
    Contextual tel (Constant tyConType (Data dataCons)) ->
      let sig = mkSig tel
          dataCons' = dataCons ++ [Const dataConName]
      in sigInsertDefinition sig tyCon $
         Contextual tel $ Constant tyConType (Data dataCons')
    _ ->
      __IMPOSSIBLE__
  where
    tyCon = opndKey tyCon0
    def' tel = Contextual tel $ DataCon (Const tyCon) numArgs ctxtType
    mkSig tel = sigAddDefinition sig0 dataConName $ def' tel

sigAddRecordConSignature
  :: Signature t -> RConName -> Opened TyConName t -> Natural -> Contextual t (Type t) -> Signature t
sigAddRecordConSignature sig0 dataConName tyCon0 numArgs ctxtType =
  case sigGetDefinition sig0 tyCon of
    Contextual tel' (Constant _ (Record _ _)) ->
      mkSig tel'
    _ ->
      __IMPOSSIBLE__
  where
    tyCon = opndKey tyCon0
    def' tel = Contextual tel $ DataCon (Const tyCon) numArgs ctxtType
    mkSig tel = sigAddDefinition sig0 dataConName $ def' tel

sigAddModule
  :: Signature t -> QName -> Tel t -> Module t -> Signature t
sigAddModule sig n args names =
  sigAddDefinition sig n $ Contextual args $ Module names

-- | Gets the type of a 'Meta'.  Fails if the 'Meta' if not
-- present.
sigGetMetaType
  :: (IsTerm t) => Signature t -> Meta -> Closed (Type t)
sigGetMetaType sig mv = case HMS.lookupValue mv (sigMetasTypes sig) of
  Just type_ -> type_
  Nothing    -> __IMPOSSIBLE__

sigLookupMetaBody
  :: Signature t -> Meta -> Maybe (MetaBody t)
-- We first check membership in the metaset. It is smaller so it should be more cache-efficient.
sigLookupMetaBody sig mv | sigMetaIsInstantiated sig mv = Just$ let !(Just mvb) = HMS.lookupValue mv (sigMetasBodies sig) in mvb
                         | otherwise                    = Nothing

sigMetaIsInstantiated
  :: Signature t -> Meta -> Bool
sigMetaIsInstantiated sig mv = I.member mv (sigMetasInstantiated sig)

sigMetasAreInstantiated :: Signature t -> MetaSet -> Bool
sigMetasAreInstantiated sig mvs = I.overlap mvs (sigMetasInstantiated sig)

sigDefinitionsAreInstantiated :: Signature t -> ISet QName -> Bool
sigDefinitionsAreInstantiated sig qs = I.overlap qs (sigDefinitionsInstantiated sig)

-- | Creates a new 'Meta' with the provided type.
--   Invariant: The number of a new meta is larger than the number of all
--   existing metas.
sigAddMeta :: Signature t -> SrcLoc -> Closed (Type t) -> (Meta, Signature t)
sigAddMeta sig0 !loc !type_ =
  (mv,) $! sig0{ sigMetasTypes = HMS.insertValue mv type_ $! sigMetasTypes sig0
               , sigMetasCount = newCount
               }
  where
    !mv = MV newCount loc
    !newCount = sigMetasCount sig0 + 1

-- | Largest possible index of an existing meta.
--   Note that a meta with this index might not actually exist, and
--   a new meta with this index may be defined in the future.
sigDefinedMetaMaxBound :: Signature t -> Int
sigDefinedMetaMaxBound = sigMetasCount

-- | Instantiates the given 'Meta' with the given body.  Fails if no
-- type is present for the 'Meta'.
sigInstantiateMeta :: Signature t -> Meta -> MetaBody t -> Signature t
sigInstantiateMeta sig !mv !t = case HMS.lookup mv $! sigMetasTypes sig of
  Just _  -> sig{sigMetasBodies = HMS.insertValue mv t $! sigMetasBodies sig
                ,sigMetasInstantiated = I.insert mv $! sigMetasInstantiated sig}
  Nothing -> __IMPOSSIBLE__

sigDefinedNames :: Signature t -> [QName]
sigDefinedNames sig = HMS.keys $! sigDefinitions sig

sigDefinedMetas :: Signature t -> [Meta]
sigDefinedMetas sig = HMS.keys $! sigMetasTypes sig

sigUninstantiatedMetas :: Signature t -> [Meta]
sigUninstantiatedMetas sig = [ mv | mv <- sigDefinedMetas sig
                                  , not$ sigMetaIsInstantiated sig mv ]

sigInstantiatedMetas :: Signature t -> [(Meta, MetaBody t)]  
sigInstantiatedMetas sig = HMS.toListValues $! sigMetasBodies sig

-- Prettify
---------------------------------------------------------------

-- Q: Why do I need to repeat the functor constraint here?
-- A: https://ghc.haskell.org/trac/ghc/ticket/11762 
instance (MonadTerm t m, Functor m) => ISetMemberM m QName where  
  full qNameId = do
    Signature{sigDefinitions} <- askSignature
    case HMS.lookupWithKey q sigDefinitions of
      Nothing     -> return q
      Just (q',_) -> return q'
    where
      q = QName{qNameId, qNameName, qNameModule = []}
      nameString = "QName#" ++ show qNameId 
      qNameName = Name { nameLoc = mempty, nameString } 

instance (MonadTerm t m, Functor m) => ISetMemberM m Meta where  
  full mvId = do
    Signature{sigMetasTypes} <- askSignature
    case HMS.lookupWithKey mv sigMetasTypes of
      Nothing -> fail$ "Meta " ++ show mv ++ " not found in signature"
      Just (mv',_) -> return mv'
    where
      mv = MV mvId noSrcLoc

class ISetMemberTermM a where
  iSetMemberTermM :: (MonadTerm t m) => ISet a -> m (Dict (ISetMemberM m a))
  -- Just the Dict would be enough, but adding the extra arguments helps with
  -- type inference.

instance ISetMemberTermM Meta where iSetMemberTermM _ = return Dict
instance ISetMemberTermM QName where iSetMemberTermM _ = return Dict

instance PrettyM t Guard where
  prettyPrecM n (Guard guardMetas guardOpenDefs) =
    prettyPrecM n =<<
      (++) <$> (map @_ @(PrettyMWrapper t) PrettyM <$> I.toList guardMetas)
           <*> (map @_ @(PrettyMWrapper t) PrettyM <$> I.toList guardOpenDefs)

-- Context
------------------------------------------------------------------------

data CtxType t where
  Type   :: !(Type t) -> CtxType t
  Dagger :: !(Type t) -> !(Type t) -> CtxType t
  deriving (Show, Eq, Functor, Foldable, Traversable, Generic)
instance Hashable t => Hashable (CtxType t)

instance ApplySubst t t => ApplySubst t (CtxType t) where
instance TraverseOpen t (CtxType t) where
  traverseOpen (Type t)     TraverseEnv{traverseTerm} = Type <$> traverseTerm t
  traverseOpen (Dagger a b) TraverseEnv{traverseTerm} = Dagger <$> traverseTerm a <*> traverseTerm b

instance Nf t a => Nf t (CtxType a) where nf = traverse nf

-- | A 'Ctx' is a backwards list of named terms, each scoped over all
-- the previous ones.
data Ctx t
  = C0
  | !(Ctx t) :< !(Name, t)
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable, Generic)
instance Hashable t => Hashable (Ctx t)

instance Nf t a => Nf t (Ctx a) where nf = traverse nf
instance ExpandMetas t a => ExpandMetas t (Ctx a) where expandMetas = traverse expandMetas

type ICtx t = Ctx (Var, t)
-- data ICtx t
--   = IC0
--   | !((ICtx t), (Ctx t)) :</ !(Named Var, t)
--   deriving (Eq, Show, Typeable, Functor, Generic)
-- instance Hashable t => Hashable (ICtx t)

type Ctx_ t = Ctx (CtxType t)
type ICtx_ t = ICtx (CtxType t)

instance Monoid (Ctx t) where
  mempty = C0

instance Semigroup (Ctx t) where
  ctx1 <> C0              = ctx1
  ctx1 <> (ctx2 :< type_) = (ctx1 <> ctx2) :< type_

ctxSingleton :: Name -> t -> Ctx t
ctxSingleton name t = C0 :< (name, t)

ctxLength :: Ctx t -> Natural
ctxLength C0         = 0
ctxLength (ctx :< _) = 1 + ctxLength ctx

ctxWeaken :: (MonadTerm t m) => Natural -> Ctx t -> t -> m t
ctxWeaken ix ctx t = weaken ix (ctxLength ctx) t

ctxWeaken_ :: (MonadTerm t m) => Ctx t -> t -> m t
ctxWeaken_ = ctxWeaken 0

ctxLookupNameIdx :: Name -> Ctx a -> Maybe Var
ctxLookupNameIdx n = go 0
  where
    go _ C0 =
      Nothing
    go ix (ctx :< (n', _type)) =
      if n == n'
      then Just $ mkVar n ix
      else go (ix + 1) ctx

ctxLookupName :: (MonadTerm t m, ApplySubst t a) => Name -> Ctx a -> m (Maybe (Var, a))
ctxLookupName n = go 0
  where
    go _ C0 =
      return Nothing
    go ix (ctx :< (n', type_)) =
      if n == n'
      then Just . (mkVar n ix, ) <$> weaken_ (ix + 1) type_
      else go (ix + 1) ctx

ctxLookupVar :: (MonadTerm t m, ApplySubst t a) => Var -> Ctx a -> m (Maybe a)
ctxLookupVar v _ | varIndex v < 0 =
  error "lookupVar: negative argument"
ctxLookupVar v ctx0 =
  case go (varIndex v) ctx0 of
    Nothing    -> return Nothing
    Just (type_) -> Just <$> weaken_ (varIndex v + 1) type_
  where
    go _ C0 =
      Nothing
    go i (ctx :< (_, type_)) =
      if i == 0
        then Just type_
        else go (i - 1) ctx

ctxGetVar :: (MonadTerm t m, ApplySubst t a) => Var -> Closed (Ctx a) -> m a
ctxGetVar v ctx = do
  mbT <- ctxLookupVar v ctx
  case mbT of
    Nothing -> __IMPOSSIBLE__
    Just t  -> return t

ctxNameVar :: Var -> Ctx a -> Maybe Name
ctxNameVar _ C0 = Nothing 
ctxNameVar (V 0) (_ :< (name, _)) = Just name
ctxNameVar (V i) (ctx' :< _) = ctxNameVar (V (i-1)) ctx'

-- | Collects all the variables in the 'Ctx'.
ctxVars :: Ctx α -> [Var]
ctxVars = reverse . go 0
  where
    go _  C0                 = []
    go ix (ctx :< (name, _)) = mkVar name ix : go (ix + 1) ctx

-- | Indexes the variables in a 'Ctx'
ctxIndexed :: Ctx t -> ICtx t
ctxIndexed = go 0
  where
    go _ C0 = C0
    go ix (ctx :< (name, t)) = let ictx = go (ix + 1) ctx in ictx :< (name, (mkVar name ix, t))

ctxUnindex :: ICtx t -> Ctx t
ctxUnindex = fmap snd

-- | Creates a 'Pi' type containing all the types in the 'Ctx' and
-- terminating with the provided 't'.
ctxPi :: (MonadTerm t m) => Ctx (Type t) -> Type t -> m (Type t)
ctxPi ctx0 = go ctx0
  where
    go C0                   t = return t
    go (ctx :< (n, type_)) t = go ctx =<< pi type_ (Abs n t)

-- | Creates a 'Lam' term with as many arguments there are in the
-- 'Ctx'.
ctxLam :: (MonadTerm t m) => Ctx (Type t) -> Term t -> m (Term t)
ctxLam ctx0 = go ctx0
  where
    go C0         t = return t
    go (ctx :< (name,_)) t = go ctx =<< lam (Abs name t)

ctxApp :: (MonadTerm t m) => m (Term t) -> Ctx (Type t) -> m (Term t)
ctxApp t ctx0 = do
  t' <- t
  eliminate t' . map Apply =<< mapM var (ctxVars ctx0)

-- Telescope
------------------------------------------------------------------------

-- | A 'Tel' is a list of types, each one ranging over the rest of the
-- list, and with something of at the end -- the inverse of a 'Ctx.Ctx',
-- plus the end element.
data Tel t
  = T0
  | !(Name, t) :> Tel t
  deriving (Show, Eq, Functor, Foldable, Traversable)

type Tel_ t = Tel (CtxType t)

instance Monoid (Tel t) where
  mempty = T0

instance Semigroup (Tel t) where
  T0 <> tel2 = tel2
  (type_ :> tel1) <> tel2 = type_ :> (tel1 <> tel2)

telLength :: Tel t -> Natural
telLength T0         = 0
telLength (_ :> tel) = 1 + telLength tel

instance Nf t a => Nf t (Tel a) where nf = traverse nf
instance ExpandMetas t a => ExpandMetas t (Tel a) where expandMetas = traverse expandMetas

-- Instances
----------------------

-- To/from Ctx
--------------

ctxToTel :: Ctx t -> Tel t
ctxToTel ctx0 = go ctx0 T0
  where
    go C0             tel = tel
    go (ctx :< (n, type_)) tel = go ctx ((n, type_) :> tel)

telToCtx :: Tel t -> Ctx t
telToCtx tel0 = go C0 tel0
  where
    go ctx T0             = ctx
    go ctx (type_ :> tel) = go (ctx :< type_) tel

telAppend :: Ctx t -> Tel t -> Tel t
telAppend C0             tel = tel
telAppend (ctx :< type_) tel = telAppend ctx (type_ :> tel)

instance (TraverseOpen t a, ApplySubst t a) => ApplySubst t (Tel a) where
instance (TraverseOpen t a) => TraverseOpen t (Tel a) where
  traverseOpen t rho@TraverseEnv{traverseLift} = go t
    where
      go T0 = do
        pure T0
      go ((n, type_) :> tel) = do
        type' <- traverseOpen type_ rho
        tel' <- traverseLift 1 $ go tel
        return $ (n, type') :> tel'

-- | Instantiates an 'Tel' repeatedly until we get to the bottom of
-- it.  Fails If the length of the 'Tel' and the provided list don't
-- match.
telDischarge :: (MonadTerm t m) => Tel t -> Term t -> [Term t] -> m t
telDischarge tel' t args =
  if telLength tel' == length args
  then instantiate t args
  else error "Term.Telescope.discharge"

telPi :: (MonadTerm t m) => Tel (Type t) -> Type t -> m (Type t)
telPi = ctxPi . telToCtx


telVars :: forall t. (IsTerm t) => Tel (Type t) -> [Var]
telVars = ctxVars . telToCtx

telApp :: (MonadTerm t m) => m (Term t) -> Tel (Type t) -> m (Term t)
telApp t tel = do
  t' <- t
  eliminate t' . map Apply =<< mapM var (telVars tel)

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

-- Smart constructors
------------------------------------------------------------------------

subId :: IsTerm t => Subst t
subId = Id

subSingleton :: (MonadTerm t m, IsTerm t) => Term t -> m (Subst t)
subSingleton t = subInstantiate t subId

subWeaken :: IsTerm t => Natural -> Subst t -> Subst t
subWeaken 0 rho                = rho
subWeaken n (Weaken m rho)     = Weaken (n + m) rho
subWeaken n (Strengthen m rho) = case n - m of
                                   0         -> rho
                                   k | k > 0 -> Weaken k rho
                                   k         -> Strengthen k rho
subWeaken n rho                = Weaken n rho

subStrengthen :: IsTerm t => Natural -> Subst t -> Subst t
subStrengthen 0 rho                = rho
subStrengthen n (Strengthen m rho) = Strengthen (m + n) rho
subStrengthen n (Weaken m rho)     = case n - m of
                                       0         -> rho
                                       k | k < 0 -> Strengthen k rho
                                       k         -> Weaken k rho
subStrengthen n rho                = Strengthen n rho

subInstantiate :: (MonadTerm t m, IsTerm t) => Term t -> Subst t -> m (Subst t)
subInstantiate t rho = do
  tView <- view t
  return $ case (tView, rho) of
    (App (Var v) [], Weaken m sgm) | varIndex v + 1 == m ->
      subWeaken (m-1) $ subLift 1 sgm
    _ ->
      Instantiate t rho

subLift :: IsTerm t => Natural -> Subst t -> Subst t
subLift n _            | n < 0 = error "lift.impossible"
subLift 0 rho          = rho
subLift _ Id           = Id
subLift k (Lift n rho) = Lift (n + k) rho
subLift k rho          = Lift k rho

subNull :: IsTerm t => Subst t -> Bool
subNull Id = True
subNull _  = False

-- | Note that the list is in reverse order
--   Is this well typed?
subFromList :: IsTerm t => Bwd (Term t) -> Subst t
subFromList ts = go 0 ts
  where
    go i B0 = subWeaken i Id
    go i (ts :. t) = (go (i+1) ts) :# t

-- Operations
------------------------------------------------------------------------

subDrop :: IsTerm t => Natural -> Subst t -> Subst t
subDrop n rho                 | n <= 0 = rho
subDrop n Id                  = subWeaken n subId
subDrop n (Weaken m rho)      = subWeaken m (subDrop n rho)
subDrop n (Instantiate _ rho) = subDrop (n - 1) rho
subDrop n (Strengthen m rho)  = subDrop (n - m) rho
subDrop _ (Lift 0 _)          = error "drop.Lift"
subDrop n (Lift m rho)        = subWeaken 1 $ subDrop (n - 1) $ subLift (m - 1) rho

subChain
  :: (MonadTerm t m)
  => Subst t -> Subst t -> m (Subst t)
subChain = flip subCompose

subCompose
  :: (MonadTerm t m)
  => Subst t -> Subst t -> m (Subst t)
subCompose rho Id =
  return rho
subCompose Id  rho =
  return rho
subCompose rho (Weaken n sgm) =
  subCompose (subDrop n rho) sgm
subCompose rho (Instantiate u sgm) =
  join $ subInstantiate <$> applySubst u rho <*> subCompose rho sgm
subCompose rho (Strengthen n sgm) =
  subStrengthen n <$> subCompose rho sgm
subCompose _ (Lift 0 _) =
  error "subCompose.Lift 0"
subCompose (Instantiate u rho) (Lift n sgm) =
  join $ subInstantiate u <$> subCompose rho (subLift (n - 1) sgm)
subCompose rho (Lift n sgm) =
  join $ subInstantiate <$> subUnsafeLookup (boundVar ("_" :: Name)) rho
                        <*> subCompose rho (subWeaken 1 (subLift (n - 1) sgm))

subUnsafeLookup
  :: (MonadTerm t m) => Var -> Subst t -> m (Term t)
subUnsafeLookup v rho = do
  mbT <- runSafeApplySubst $ subLookup v rho
  case mbT of
    Left n  -> error $ "unsafeLookup: free name " ++ show n
    Right t -> return t

subLookup :: forall t m. (MonadTerm t m) => Var -> Subst t -> ApplySubstM m (Term t)
subLookup = inline subLookup_ Nothing

subLookupTwin :: forall t m. (MonadTerm t m) => Dir -> Var -> Subst t -> ApplySubstM m (Term t)
subLookupTwin = inline subLookup_ . Just

subLookup_ :: forall t m. (MonadTerm t m) => Maybe Dir -> Var -> Subst t -> ApplySubstM m (Term t)
subLookup_ dir v0 rho0 = go rho0 (varIndex v0)
  where
    nm = v0

    go :: Subst t -> Natural -> ApplySubstM m (Term t)
    go rho i = case rho of
      Id -> do
        lift $ var_ dir v
      Weaken n Id -> do
        let j = i + n
        lift $ var_ dir $ mkVar "nm" j
      Weaken n rho' -> do
        lift . (`applySubst` subWeaken n subId) =<< go rho' i
      Instantiate u rho' -> do
        if i == 0 then case dir of
            Nothing -> return u
            Just _  -> do
              
              throwError nm
        else go rho' (i - 1)
      Strengthen n rho' -> do
        if i >= n
          then go rho' (i - n)
          else throwE nm
      Lift n rho' -> do
        if i < n
          then lift $ var_ dir v
          else lift . (`applySubst` subWeaken n subId) =<< go rho' (i - n)
      where
        v = mkVar "nm" i

-- Twin variable substitutions --
---------------------------------

class HasVar t where
  varP :: Maybe Dir -> Natural -> t

  {-# INLINE varP #-}
  default varP :: IsTerm t => Maybe Dir -> Natural -> t
  varP dir = runIdentity . var_ dir . V     

{-# INLINE atDir #-}
atDir :: MonadUnview t m => Maybe Dir -> t -> m t
atDir Nothing    t = pure t
atDir (Just dir) t = view t >>= \case
                       App  (Var v) []  -> unview$ App (Twin dir v) []
                       _                -> __IMPOSSIBLE__

-- Operations on terms
------------------------------------------------------------------------

weaken :: (IsTerm t, ApplySubst t a, MonadTerm t m) => Natural -> Natural -> a -> m a
weaken from by t = applySubst t $ subLift from $ subWeaken by subId

weaken_ :: (IsTerm t, ApplySubst t a, MonadTerm t m) => Natural -> a -> m a
weaken_ n t = weaken 0 n t

strengthen :: (MonadTerm t m) => Natural -> Natural -> t -> m t
strengthen from by t =
  applySubst t $ subLift from $ subStrengthen by subId

strengthen_ :: (MonadTerm t m) => Natural -> t -> m t
strengthen_ = strengthen 0

instantiate_ :: (IsTerm t, PrettyM t a, ApplySubst t a, MonadTerm t m) => Abs a -> Term t -> m a
instantiate_ body arg = instantiate (unAbs body) [arg]

instantiate :: (IsTerm t , ApplySubst t a, PrettyM t a, MonadTerm t m) => a -> [Term t] -> m a
instantiate t0 ts0 = do
  let msg = do
        t0Doc <- prettyM_ t0
        ts0Doc <- prettyM_ ts0
        return$ "t:"  //> t0Doc  $$
                "as:" //> ts0Doc
  debugBracket DL.Instantiate msg $
    debugResult "result:" $ applySubst t0 =<< go (reverse ts0)
  where
    go []       = return subId
    go (t : ts) = subInstantiate t =<< go ts

getAbsName :: (Monad m) => Abs t -> m (Maybe Name)
getAbsName t = getAbsName_ t <&> \case
                           "_"  -> Nothing
                           name -> Just name
 
getAbsName_ :: (Monad m) => Abs t -> m Name
getAbsName_ t = return$ absName t

-- Free variables
------------------

-- * Reporting occurences
newtype DoesNotOccur = OR (FreeLattice Guard)
  deriving (MeetSemiLattice, JoinSemiLattice, BoundedMeetSemiLattice, BoundedJoinSemiLattice,DecBottom,DecTop)

deriving instance PrettyM t DoesNotOccur

{-# COMPLETE Flexibly #-}
-- | The (meta)variable does not occur
pattern DoesNotOccur :: DoesNotOccur
-- | The variable occurs, and will occur in all normalized forms
pattern Rigidly      :: DoesNotOccur
-- | The variable occurs, but may cease to occur in case of the guard
--   becoming instantiated.
pattern Flexibly     :: GuardLattice -> DoesNotOccur

pattern DoesNotOccur = OR Top     -- does not occur
pattern Rigidly      = OR Bottom  -- occurs  
pattern Flexibly bs  = OR bs      -- occurs, but perhaps not if …

flexibleUnder :: Guard -> DoesNotOccur -> DoesNotOccur
flexibleUnder mvs = \case
  DoesNotOccur -> DoesNotOccur
  Rigidly      -> Flexibly (inj mvs)
  Flexibly bs  -> Flexibly (inj mvs \/ bs)

data FreeVarSet = FreeVarSet
  { fvRigid    :: !VarSet
  , fvFlexible :: !VarSet
  }

instance Monoid FreeVarSet where
  mempty = FreeVarSet B.empty B.empty

instance Semigroup FreeVarSet where
  FreeVarSet rigid1 flex1 <> FreeVarSet rigid2 flex2 =
    FreeVarSet (rigid1 <> rigid2) (flex1 <> flex2)

class FreeVars t a | a -> t where
  freeVars  :: MonadFreeVars t m => a -> m FreeVarSet
  -- isVarFree :: a -> ReaderT Var m DoesNotOccur

-- Elimination
------------------------------------------------------------------------


-- | Tries to apply the eliminators to the term.  Throws an error
-- when the term and the eliminators don't match.
eliminate :: (MonadTerm t m) => t -> [Elim t] -> m t
eliminate t elims = do
  reduce <- confWhnfEliminate <$> readConf
  tView <- if reduce then whnfView t else view t
  let badElimination = do
        tDoc <- prettyM_ t
        elimsDoc <- prettyM_ elims
        fatalError $ PP.render $
          "Bad elimination" $$
          "term:" //> tDoc $$
          "elims:" //> elimsDoc
  case (tView, elims) of
    (_, []) ->
        return t
    (Con _c args, Proj proj : es) -> do
        let ix = pField proj
        if unField ix >= length args
          then badElimination
          else eliminate (args !! unField ix) es
    (Lam body, Apply argument : es) -> do
        body' <- instantiate_ body argument
        eliminate body' es
    (App h es1, es2) ->
        app h (es1 ++ es2)
    (_, _) ->
        badElimination

{-
data OpenedItem t = OpenedItem
  { oiArguments :: ![Term t]
  , oiWeakenBy  :: !Natural
  }

-- | Here we store definitions that have been opened -- specifically, if
-- some definition is under a context with n variables, its entry here
-- should contain the n terms to apply to it to eliminate the context.
data Opened t
  = ONil
  | OSnoc (Opened t)
          -- The number of abstractions we went past to get to this point.
          !Natural
          -- The things we've opened -- note that we don't have
          -- 'Contextual' anymore.
          !(HMS.HashMap Name (Definition t))
-}

-- Clauses invertibility
------------------------

termHead :: (IsTerm t, MonadTerm t m) => t -> m (Maybe TermHead)
termHead t = do
  tView <- whnfView t
  case tView of
    App (Def (OPDef f)) _  -> return $ Just $ DefHead $ getQName $ opndKey f
    App (Def (OTyCon f)) _ -> return $ Just $ DefHead $ getQName $ opndKey f
    App{} -> do
      return Nothing
    Con (ODCon f) _ ->
      return $ Just $ DefHead $ getQName $ opndKey f
    Con (ORCon _) _ ->
      -- Records are not invertible, because of η
      return Nothing
    Pi{} ->
      return $ Just $ PiHead
    Lam{} ->
      return Nothing
    Refl{} ->
      return Nothing
    Set{} ->
      return Nothing
    Equal{} ->
      return Nothing

checkInvertibility
  :: (IsTerm t, MonadTerm t m) => [Closed (Clause t)] -> m (Closed (Invertible t))
checkInvertibility = go []
  where
    go injClauses [] =
      return $ Invertible $ reverse injClauses
    go injClauses (clause@(Clause _ cbody) : clauses) = do
      let fallback = return $ NotInvertible $ reverse (map snd injClauses) ++ (clause : clauses)
      case cbody of
        ClauseBody body -> do
          th <- termHead body
          case th of
            Just tHead | Nothing <- lookup tHead injClauses ->
              go ((tHead, clause) : injClauses) clauses
            _ ->
              fallback
        _ ->
          fallback

-- Pretty instances
-- ================

debugResult :: (MonadTerm t m, PrettyM t b) => String -> m b -> m b
debugResult label m = do
  b <- m
  debug (fromString label) (prettyM_ b)
  return b

instance (ForAllQName (PrettyM t) f t, PrettyM t (f Projection t)) => PrettyM t (Definition f t) where
  prettyM (Constant type_ Postulate) = do
    typeDoc <- prettyM type_
    return $ "postulate" //> typeDoc
  prettyM (Constant type_ (Function instk)) = do
    typeDoc <- prettyM type_
    instDoc <- prettyM instk
    return $ typeDoc $$ instDoc
  prettyM (Constant type_ (Data dataCons)) = do
    typeDoc <- prettyM type_
    dataConsDocs <- mapM prettyM dataCons
    return $ "data" <+> typeDoc <+> "where" $$> PP.vcat dataConsDocs
  prettyM (Constant type_ (Record dataCon fields)) = do
    typeDoc <- prettyM type_
    dataConDoc <- prettyM dataCon
    fieldsDoc <- mapM prettyM fields
    return $ "record" <+> typeDoc <+> "where" $$>
             "constructor" <+> dataConDoc $$
             "field" $$> PP.vcat fieldsDoc
  prettyM (DataCon tyCon _ (Contextual pars type_)) = do
    tyConDoc <- prettyM tyCon
    typeDoc <- prettyM =<< telPi pars type_
    return $ "constructor" <+> tyConDoc $$> typeDoc
  prettyM (Projection _ tyCon (Contextual pars type_)) = do
    tyConDoc <- prettyM tyCon
    typeDoc <- prettyM =<< telPi pars type_
    return $ "projection" <+> tyConDoc $$> typeDoc
  prettyM (Module (Contextual tel names)) = do
    telDoc <- prettyM tel
    return $ "module" <+> telDoc <+> PP.tupled (map PP.pretty (HS.toList names))

instance PrettyM t (Clause t) where
  prettyM (Clause pats body) = do
    patsDoc <- mapM prettyM pats
    case body of
      ClauseNoBody ->
        return $ PP.group $ PP.hsep patsDoc
      ClauseBody t -> do
        bodyDoc <- prettyM t
        return $ PP.group $
          PP.hsep (patsDoc ++ ["="]) //> bodyDoc

instance PrettyM t Name where
  prettyM = return . PP.pretty

instance PrettyM t QName where
  prettyM = return . PP.pretty

instance PrettyM t (Pattern t) where
  prettyM e = case e of
    VarP      -> return $ PP.text "_"
    ConP c es -> do cDoc <- prettyM c
                    esDoc <- mapM prettyM es
                    return $ prettyApp 10 cDoc esDoc
    EmptyP    -> return $ PP.text "()"

prettyApp :: PP.Pretty a => Int -> PP.Doc -> [a] -> PP.Doc
prettyApp _ h []   = h
prettyApp p h args = PP.condParens (p > 3) $ h </> PP.fillSep (map (PP.prettyPrec 4) args)

instance PrettyM t a => PrettyM t (Tel a) where
  prettyM tel00 = localCtx C0$ fmap PP.group $ case tel00 of
    T0 -> do
      return "[]"
    (n0, type0) :> tel0 -> do
      type0Doc <- prettyM type0
      tel0Doc <- localAddName n0$ go tel0
      return $ "[" <+> PP.pretty n0 <+> ":" <+> type0Doc <> whichLine tel0 <> tel0Doc
    where
      go T0 = do
        return "]"
      go ((n, type_) :> tel) = do
        typeDoc <- prettyM type_
        telDoc <- localAddName n$ go tel
        return $ ";" <+> PP.pretty n <+> ":" <+> typeDoc <> whichLine tel <> telDoc

      whichLine T0 = PP.line
      whichLine _  = PP.linebreak

instance PrettyM t a => PrettyM t (Ctx a) where
  prettyM = prettyM . ctxToTel

instance IsTerm t => PrettyM t (Subst t) where
  prettyM sub0 = case sub0 of
    Sub.Id -> do
      return "Id"
    Sub.Weaken i sub -> do
      subDoc <- prettyM sub
      return $ "Weaken" <+> PP.pretty i //> subDoc
    Sub.Instantiate t sub -> do
      subDoc <- prettyM sub
      tDoc <- prettyM t
      return $
        "Instantiate" $$
        "term:" //> tDoc $$
        "sub:" //> subDoc
    Sub.Strengthen i sub -> do
      subDoc <- prettyM sub
      return $ "Strengthen" <+> PP.pretty i //> subDoc
    Sub.Lift i sub -> do
      subDoc <- prettyM sub
      return $ "Lift" <+> PP.pretty i //> subDoc

instance PrettyM t (FunInst t) where
  prettyM Open = do
    return "Open"
  prettyM (Inst t) = do
    tDoc <- prettyM t
    return $ "Inst" //> tDoc

instance PrettyM t (Invertible t) where
  prettyM = prettyM . ignoreInvertible

instance PrettyM t (MetaBody t) where
  prettyM (MetaBody n t) = go n []
    where
      go 0 acc = do
        accDoc <- mapM (prettyM @_ @t) (reverse acc)
        tDoc <- prettyM t 
        return$ PP.separated mempty accDoc <+> ":=" <+> tDoc
      go n acc = do
        v <- var$ mkVar "_" (n-1)
        localAddName "_"$ go (n-1) (v:acc) 

instance PrettyM t (BlockedHead t) where
  prettyM (BlockedOnFunction n) = do
    nDoc <- prettyM n
    return $ "BlockedOnFunction" //> nDoc
  prettyM BlockedOnJ = do
    return "BlockedOnJ"

instance (PrettyM t a, PrettyM t b) => PrettyM t (a, b) where
  prettyM (x, y) = do
    xDoc <- prettyM x
    yDoc <- prettyM y
    return $ PP.tupled [xDoc, yDoc]

instance (PrettyM t a) => PrettyM t (Contextual t a) where
  prettyM (Contextual tel x) = do
    telDoc <- prettyM tel
    xDoc <- prettyM x
    return $
      "tel:" //> telDoc $$
      "inside:" //> xDoc

instance (PrettyM t a) => PrettyM t (Const a b) where
  prettyM (Const x) = prettyM x

instance PrettyM t Projection where
  prettyM = return . PP.pretty

instance (PrettyM t a, PrettyM t b) => PrettyM t (a :∈ b) where
  prettyM (x :∈ y) = do
    xDoc <- prettyM x
    yDoc <- prettyM y
    return $ xDoc //> "∈" //> yDoc

instance (PrettyM t a) => PrettyM t (CtxType a) where
  prettyM (Type t) = prettyM t
  prettyM (Dagger a b) = do
    aDoc <- prettyM a
    bDoc <- prettyM b
    return$ aDoc //> "‡" //> bDoc

instance (PrettyM t a) => PrettyM t (Head a) where
  prettyM (Var v) = prettyM v
  prettyM (Twin dir v) = do
    name <- varName v
    return$ fromString$
                           PP.render (varIndex v) <>
                           PP.render dir <> "#" <> PP.render name
  prettyM (Def o) = prettyM o
  prettyM (Meta mv) = prettyM mv
  prettyM (J) = return "J"

instance PrettyM t t => PrettyM t (Signature t) where
  prettyM Signature{} = return "«signature»"

instance PrettyM t a => PrettyM t (Maybe a) where
  prettyPrecM  _  Nothing   = return "*"
  prettyPrecM  s  (Just a)  = prettyPrecM s a

instance PrettyM t a => PrettyM t (FreeLattice a) where
  prettyPrecM = prettyPrecFLM prettyPrecM

instance PrettyM t a => PrettyM t (DefSorted a) where
  prettyM (DefName _ a) = prettyM a
  prettyPrecM p (DefName _ a) = prettyPrecM p a

instance PrettyM t a => PrettyM t (ConSorted a) where
  prettyM (ConName _ a) = prettyM a
  prettyPrecM p (ConName _ a) = prettyPrecM p a

-- * Twins
class IsTerm t => HasSubterms t a where
  traverseSubterms :: (MonadTerm t m) => a -> (t -> m t) -> m a

instance (HasSubterms t a, HasSubterms t b) => HasSubterms t (a,b) where
  traverseSubterms (a,b) f = (,) <$> traverseSubterms a f <*> traverseSubterms b f

instance (HasSubterms t a, HasSubterms t b) => HasSubterms t (a :∈ b) where
  traverseSubterms (a :∈ b) f = (:∈) <$> traverseSubterms a f <*> traverseSubterms b f

instance IsTerm t => HasSubterms t Meta where
  traverseSubterms mv _ = pure mv

instance IsTerm t => HasSubterms t t where
  traverseSubterms = flip ($)

instance (HasSubterms t a, Traversable f) => HasSubterms t (f a) where
  traverseSubterms x f = traverse (flip traverseSubterms f) x


