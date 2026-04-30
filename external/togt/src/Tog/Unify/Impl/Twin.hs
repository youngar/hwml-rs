{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Tog.Unify.Impl.Twin
  (module Tog.Unify.Class
  ,Twin
  ,Constraint(..)
  ,TwinT'(..)
  ) where

import           Tog.Prelude
import           Tog.PrettyPrint                  (($$), (<+>), (//>), (//), group, hang)
import           Tog.Term

import           Tog.Monad
import           Tog.Unify.Common hiding (etaExpand, checkMetaArg, checkMetaElims, intersectMetaSpine, etaExpandMeta)

import           Tog.Unify.Class
import           Tog.Term.MetaVars

import           Tog.Names
import           Tog.Names.Sorts

import qualified Data.BitSet as B
import           Data.PhysEq

import           Tog.Instrumentation
import qualified Tog.Instrumentation.Debug.Label as DL

import qualified Tog.PrettyPrint as PP

-- import           Development.Placeholders

import           Data.Ord (Down(..))

import           Data.FreeLattice (inj, meetsM, joinsM, fromBool, DecBottom(..), DecTop(..), censorJoin)
import           Data.Sequence (Seq(Empty, (:<|), (:|>)))
import qualified Data.Sequence as Seq
import           Data.Either (partitionEithers)

#include "impossible.h"

-- | Symbol that gives name to the unifier
data Twin

type C t = Constraint Twin t
type Cs t = Constraints Twin t 

type UFW t a = UF Twin t a
type UFW_ t r = UF_ Twin t r

type UFR t = UFW t (Cs t)
type UFR_ t r = UFW_ t r (Cs t)


type CtxT' b t = Ctx (TwinT' b t)
type ICtxT' b t = ICtx (TwinT' b t)

type CtxT t = CtxT' () t
type CtxTC t = CtxT' Bool t
type ICtxTC t = ICtx (TwinTypeC t)

type TelT' b t = Tel (TwinT' b t)
type TelT t = TelT' () t
type TelTC t = TelT' Bool t

type TwinTC = TwinT' Bool
type TwinType = TwinT
type TwinTypeC = TwinTC

forgetN :: TwinT' b t -> TwinT t
forgetN (SingleT a) = SingleT a
forgetN TwinT{lty,rty,constraint} = TwinT{lty,rty,constraint,necessary=()}

embedN :: TwinT t -> TwinTC t
embedN (SingleT a) = SingleT a
embedN TwinT{lty,rty,constraint} = TwinT{lty,rty,constraint,necessary=False}

type TwinTerm = TwinT
data TwinT' b t =
    SingleT t
  | TwinT {
       lty        :: t
     , rty        :: t
     , constraint :: ConstraintGuard
       -- ^ Set of constraints that are /sufficient/ for lty==rty
       -- 
       --   prop> constraint /= top
       --  
       --   Note that the constraint might become equivalent
       --   to top when the constraints contained in it are solved.
       --   But, detecting this equivalence is monadic.
     , necessary  :: b
       -- ^ Whether the constraint guard is both sufficient and necessary
     }
   deriving (Functor, Foldable, Traversable)

instance Bifunctor TwinT' where
  bimap f g (SingleT t) = SingleT (g t)
  bimap f g (TwinT{lty,rty,constraint,necessary}) =
    TwinT{lty=g lty,rty=g rty,constraint,necessary=f necessary}

instance IsVarNotFree t a => IsVarNotFree t (TwinT' b a) where
  isVarNotFree_ (SingleT t)       = SingleT <$> isVarNotFree_ t
  isVarNotFree_ (TwinT{lty,rty,constraint,necessary})  = do
    lty'       <- isVarNotFree_ lty
    rty'       <- isVarNotFree_ rty
    pure$ TwinT{lty=lty',rty=rty',constraint,necessary}

type TwinT = TwinT' ()

instance Nf t a => Nf t (TwinT' b a) where nf = traverse nf
instance ExpandMetas t a => ExpandMetas t (TwinT' b a) where expandMetas = traverse expandMetas
instance ExpandGuards (TwinT' b a) where
  expandGuards s@SingleT{} = pure s
  expandGuards TwinT{lty,rty,constraint,necessary} = do
    constraint' <- expandGuards constraint
    return TwinT{lty,rty,necessary,constraint = constraint'}

instance PrettyM t a => PrettyM t (TwinT a) where
  prettyM (SingleT t) = prettyM t
  prettyM TwinT{lty,rty,constraint} = do
    ltyDoc <- prettyM lty
    rtyDoc <- prettyM rty
    constraintDoc <- prettyM constraint
    return$ ltyDoc <+> "‡" <> constraintDoc <+> rtyDoc

instance PrettyM t a => PrettyM t (TwinTC a) where
  prettyM (SingleT t) = prettyM t
  prettyM TwinT{lty,rty,constraint,necessary} = do
    ltyDoc <- prettyM lty
    rtyDoc <- prettyM rty
    constraintDoc <- prettyM constraint
    return$ ltyDoc <+> "‡" <> (if necessary then "!" else mempty) <> constraintDoc <+> rtyDoc

constraintT :: TwinT' b t -> ConstraintGuard
constraintT (SingleT{}) = top
constraintT (TwinT{constraint}) = constraint

class CommuteTT a b | a -> b where commuteTT :: TwinType a -> b
instance CommuteTT (a,b) (TwinType a, TwinType b) where commuteTT = (,) <$> fmap fst <*> fmap snd
instance CommuteTT (Tel a) (Maybe (TelT a)) where
  commuteTT (SingleT a) = pure$ fmap SingleT a
  commuteTT (TwinT tel1 tel2 constraint ()) = go tel1 tel2
    where
      go T0 T0 = pure T0
      go ((name1, t1) :> x) ((_, t2) :> y) = ((name1, TwinT t1 t2 constraint ()) :>) <$> go x y
      go _  _  = Nothing

instance Eq k => CommuteTT (Opened k a) (Maybe (Opened k (TwinT a))) where
  commuteTT (SingleT t) = pure$ fmap SingleT$ t
  commuteTT (TwinT   (Opened k1 args1) (Opened k2 args2) constraint ()) = do
    if k1 == k2 && length args1 == length args2 then
      Just$ Opened k1 [TwinT a1 a2 constraint () | (a1,a2) <- zip args1 args2 ]
    else
      Nothing
  commuteTT _ = __IMPOSSIBLE__

instance CommuteTT (Head a) (Maybe (Head (TwinT a))) where
  commuteTT (SingleT h) = pure$ fmap SingleT h
  commuteTT (TwinT (Var v1)       t _ ()) | Var v2 <- t , v1 == v2        = pure$ Var v1
                                          | otherwise = Nothing

  commuteTT (TwinT (Twin dir1 v1) t _ ()) | Twin dir2 v2 <- t, v1 == v2, dir1 == dir2  = pure$ Twin dir1 v1
                                          | otherwise = Nothing

  commuteTT (TwinT (Meta m1)      t _ ()) | Meta m2 <- t     , m1 == m2                = pure$ Meta m1
                                          | otherwise = Nothing

  commuteTT (TwinT J              t _ ()) | J <- t                                     = pure J 
                                          | otherwise = Nothing

  commuteTT (TwinT (Def o1)       t c ()) | (Def o2) <- t                              = Def <$> commuteTT (TwinT o1 o2 c ())
                                          | otherwise = Nothing

instance CommuteTT (Ctx a) (Maybe (Ctx (TwinT a))) where
  commuteTT (SingleT ctx) = Just$ fmap SingleT ctx
  commuteTT (TwinT ctxLeft ctxRight constraint ()) = go ctxLeft ctxRight
    where
      go C0 C0 = Just C0
      go (ctxL :< (n, tL)) (ctxR :< (_n, tR)) =
        (:< (n, TwinT tL tR constraint ())) <$> go ctxL ctxR
      go _ _ = Nothing

twinLeft :: TwinT' b t -> Term t
twinLeft (SingleT t) = t
twinLeft TwinT{lty} = lty

twinRight :: TwinT' b t -> Term t
twinRight (SingleT t) = t
twinRight TwinT{rty} = rty

-- | Builds a possibly twin term.

--twinT :: t -> t -> ConstraintGuard -> TwinTerm t
--twinT l _ c | c == top = SingleT l
--twinT l r c            = TwinT{lty=l,rty=r,constraint=c}

-- | This helps work with twin terms simultaneously
--   This is the reason that we consider the constraint
--   field to be only 'sufficient' constraints, and not
--   necessary ones.
--
--   Note that, when unifying both sides of the
--   twin term becomes necessary
instance Applicative TwinTerm where
  pure = SingleT
  (SingleT f) <*> x = fmap f x
  f <*> (SingleT x) = fmap ($ x) f
  f <*> x = TwinT (twinLeft f $ twinLeft x)
                  (twinRight f $ twinRight x)
                  (constraintT f /\ constraintT x)
                  ()

instance TraverseOpen t a => ApplySubst t (TwinT' b a) where
instance TraverseOpen t a => TraverseOpen t (TwinT' b a) where
  traverseOpen t env = sequenceA$ flip traverseOpen env <$> t

instance FreeVars t t => FreeVars t (TwinT' b t) where
  freeVars = fmap (foldMap id) . traverse freeVars

-- |  Laws:
--    prop> flipTT . flipTT == id
--    prop> simplifyTT >=> simplifyTT == simplifyTT
class TT a where
  type TermTT a
  flipTT :: a -> a
  simplifyTT' :: a -> UFW (TermTT a) (a, Bool)
  simplifyTT' a = do
    a' <- simplifyTT a
    return (a', isUnifiedTT a')

  simplifyTT :: a -> UFW (TermTT a) a
  simplifyTT = fmap fst . simplifyTT'

  isUnifiedTT :: a -> Bool

  {-# MINIMAL flipTT, simplifyTT', isUnifiedTT | flipTT, simplifyTT, isUnifiedTT #-}

-- | Flips a pair of types. 
-- | prop> flipTT . flipTT == id
instance TT (TwinT' b t) where
  type TermTT (TwinT' b t) = t
  flipTT :: TwinT' b t -> TwinT' b t
  flipTT s@SingleT{} = s
  flipTT TwinT{lty,rty,constraint,necessary} = TwinT{lty=rty,rty=lty,constraint,necessary}

  simplifyTT' :: TwinT' b t -> UFW t (TwinT' b t,Bool)
  simplifyTT' r@SingleT{}                 = pure (r,True)
  simplifyTT' r@TwinT{lty,rty,constraint,necessary} = isSolved constraint >>= \case
    True  -> return (TwinT{lty,rty,constraint=Top,necessary}, True)
    False -> return (r                , False)

  isUnifiedTT SingleT{} = True
  isUnifiedTT TwinT{constraint=Top} = True
  isUnifiedTT TwinT{constraint=_}   = False

instance TT a => TT (Ctx a) where
  type TermTT (Ctx a) = TermTT a
  flipTT = fmap flipTT
  simplifyTT = traverse simplifyTT

  isUnifiedTT C0 = True
  isUnifiedTT (ctx :< (_, t)) = isUnifiedTT t && isUnifiedTT ctx

instance (TT a, TT b, TermTT a ~ TermTT b) => TT (a :∈ b) where
  type TermTT (a :∈ b) = TermTT a
  flipTT     (a :∈ b) = (flipTT a) :∈ (flipTT b)
  simplifyTT (a :∈ b) = (:∈) <$> simplifyTT a <*> simplifyTT b

instance TT (C t) where
  type TermTT (C t) = t
  flipTT (Done doc) = Done doc
  flipTT EqualTerm{ctx,lhs,rhs,ty} =
    EqualTerm{ctx = flipTT ctx
             ,ty  = flipTT ty
             ,lhs = rhs
             ,rhs = lhs
             }
  flipTT EqualHeadTerm{ctx,lhsV,rhsV,ty} =
    EqualHeadTerm{ctx = flipTT ctx
             ,ty   = flipTT ty
             ,lhsV = rhsV
             ,rhsV = lhsV
             }
  flipTT EqualStrongNeutral{ctx,ty,mbH,elims1,elims2} =
    EqualStrongNeutral{ctx = flipTT ctx
             ,ty   = flipTT ty
             ,mbH  = flipTT mbH
             ,elims1 = elims2
             ,elims2 = elims1
             }
  flipTT c@EtaExpandMeta{} = c

  simplifyTT (Done doc) = pure (Done doc)
  simplifyTT EqualTerm{ctx,lhs,rhs,ty} = do
    (ctx',r') <- simplifyTT' ctx
    ty'       <- (if r' then simplifyTT else pure) ty
    return EqualTerm{ctx=ctx',lhs,rhs,ty=ty'}
  simplifyTT EqualHeadTerm{ctx,ty,lhsV,rhsV} = do
    (ctx',r') <- simplifyTT' ctx
    ty'      <- (if r' then simplifyTT else pure) ty
    return EqualHeadTerm{ctx=ctx',ty=ty',lhsV,rhsV}
  simplifyTT EqualStrongNeutral{ctx,ty,mbH,elims1,elims2} = do
    (ctx',r') <- simplifyTT' ctx
    ty'       <- (if r' then simplifyTT else pure) ty
    mbH'      <- simplifyTT mbH
    return EqualStrongNeutral{ctx=ctx',ty=ty',mbH=mbH',elims1,elims2}
  simplifyTT c@EtaExpandMeta{} = pure c

  isUnifiedTT = return False
  
instance Eq t => Eq (TwinType t) where (==) = (==) `on` ((,) <$> lty <*> rty)
instance Hashable t => Hashable (TwinType t) where hashWithSalt s = hashWithSalt s . ((,) <$> lty <*> rty)

data CheckEqualTerm t = CheckEqualTerm {
            ctx      :: CtxTC t
          , ty       :: TwinTypeC t
          , lhs      :: Term t
          , rhs      :: Term t
          }

instance UnifierImpl Twin where
  unifierShortName = "W"
  unifierLongName  = "Twin"

instance Unify t => Unifier Twin t where

  data Constraint Twin t where
    Done      :: C t -> C t
    EqualTerm :: {
            ctx      :: CtxTC t
          , ty       :: TwinTypeC t
          , lhs      :: Term t
          , rhs      :: Term t
            -- As an optimization, we may store a list of guarded phases, so that, depending on
            -- which guard triggers, we can start directly from that phase. 
            -- , phase    :: Phase
          } -> C t

    -- | `lhsV` and `rhsV` are in WHNF
    EqualHeadTerm :: {
            ctx      :: CtxTC t
          , ty       :: TwinTypeC t  -- Type of the constraint (lhsV and rhsV)
          , lhsV     :: TermView t 
          , rhsV     :: TermView t
          } -> C t

    -- | `lhsV` and `rhsV` are in WHNF
    EqualStrongNeutral :: {
            ctx      :: CtxTC t
          , ty       :: TwinTypeC t
          , mbH      :: TwinTerm t :∈ TwinType t
          , elims1   :: Elims t 
          , elims2   :: Elims t 
          } -> C t

    -- | A constraint to instantiate a meta based on its type
    
    EtaExpandMeta :: {
         -- The meta
         mv    :: Meta
       , tel   :: Tel t
       , endTy :: Type t
       } -> C t
  
  makeConstraint (fmap SingleT -> ctx) (t1 :∈ type1) (t2 :∈ type2) = do

      -- It should not be necessary to unify the types, as this will be done
      -- when solving the constraint.
      --
      -- But!
      -- + If we have the chance to do it independently,
      --    we can glean more information that will help us complete the unification.
      -- + Sometimes we will short-cut the term unification
      --   (e.g. via syntactic equality) but we still want to unify the types.
      watching (newConstraint EqualTerm{ctx
                                       ,lhs    = type1
                                       ,rhs    = type2
                                       ,ty     = SingleT set
                                       --,phase = minBound
                                       }) $ \cty ->
           newConstraint EqualTerm{ctx
                     ,lhs    = t1
                     ,rhs    = t2
                     ,ty     = TwinT{lty=type1,rty=type2,constraint=cty,necessary=True}
                     --,phase  = minBound
                     }

  refine = fastEquality $ simplifyTT >=> maybeNf >=> \constr0 -> do
    debug "simplified:" $ runNamesT C0$ prettyM constr0
    -- Simplify those twin variables that have been solved
    case constr0 of
      Done{} -> done
      EqualTerm{ctx,lhs,rhs,ty} ->
        -- Optimization: try with simple checks first
        refineEqualTerm ctx ty lhs rhs

      EqualHeadTerm{ctx,lhsV,rhsV,ty} ->
        refineHeadEqualTerm ctx ty lhsV rhsV

      EqualStrongNeutral{ctx,ty,mbH,elims1,elims2} ->
        refineEqualStrongNeutral ctx ty mbH elims1 elims2

      EtaExpandMeta{mv,tel,endTy} -> etaExpandMeta mv tel endTy
    where
      
      fastEquality :: forall r. (C t -> UFR_ t r) -> C t -> UFR_ t r
      fastEquality κ = do
         checkPhysEq$
           checkMaybeNf$
             checkSynEq$
               κ <=< simplifyTT
      -- fastEquality κ constr = κ =<< maybeNf =<< simplifyTT constr

  newMeta mv = do
    mvTy <- getMetaType mv
    newConstraint$ EtaExpandMeta{mv,tel=T0,endTy=mvTy}

checkSynEq
  :: (Unify t)
  => (C t -> UFR_ t r) -> C t -> UFR_ t r
checkSynEq keepGoing c@EqualTerm{ctx,ty,lhs=t1,rhs=t2} =
  (confDisableSynEquality <$> readConf) >>= \case
    True  -> keepGoing c
    False -> do
        -- Optimization: try with a simple syntactic check first.
        eq <- debugBracket_ DL.CheckSynEq "" $ synEq t1 t2
        if eq
          then done
          else keepGoing c
checkSynEq keepGoing c = keepGoing c

checkMaybeNf
  :: (IsTerm t)
  => (C t -> UFR_ t r) -> C t -> UFR_ t r
checkMaybeNf keepGoing c =
  join$ keepGoing <$> maybeNf c

checkMaybeNfElseExpandMetas
  :: (Unify t)
  => (Term t -> Term t -> UFR_ t r) -> Term t -> Term t -> UFR_ t r
checkMaybeNfElseExpandMetas keepGoing t1 t2 =
  join$ keepGoing <$> maybeNfElseExpandMetas t1 <*> maybeNfElseExpandMetas t2

checkPhysEq_
  :: (IsTerm t, MonadTerm t m, MonadConf m)
  => Term t -> Term t -> m Bool
checkPhysEq_ t1 t2 =
  andM [confPhysicalEquality <$> readConf
       ,debugBracket_ DL.CheckPhysEq "" (physEq t1 t2)
       ]

checkPhysEq
  :: (Unify t)
  => (C t -> UFR_ t r) -> C t -> UFR_ t r
checkPhysEq keepGoing c@EqualTerm{ctx,ty,lhs=t1,rhs=t2} = do
  (confPhysicalEquality <$> readConf) >>= \case
    True -> do
      debugBracket_ DL.CheckPhysEq "" (physEq t1 t2) >>= \case
        True  -> done
        False -> keepGoing c
    False -> do
      keepGoing c
checkPhysEq keepGoing c = keepGoing c


instance Nf t (C t) where
  nf (Done doc) = pure (Done doc)
  nf EqualTerm{ctx,ty,lhs,rhs} = do
    ctx' <- nf ctx
    ty'  <- nf ty
    lhs' <- nf lhs
    rhs' <- nf rhs
    return EqualTerm{ctx=ctx',ty=ty',lhs=lhs',rhs=rhs'}
  nf EqualHeadTerm{ctx,ty,lhsV,rhsV} = do
    ctx'  <- nf ctx
    ty'   <- nf ty 
    lhsV' <- traverse nf lhsV
    rhsV' <- traverse nf rhsV
    return EqualHeadTerm{ctx=ctx',ty=ty',lhsV=lhsV',rhsV=rhsV'}
  nf EtaExpandMeta{mv,tel,endTy} = do
    mv'    <- {- nf -} pure mv
    tel'   <- nf tel
    endTy' <- nf endTy
    return EtaExpandMeta{mv=mv',tel=tel',endTy=endTy'}

instance ExpandMetas t (C t) where
  expandMetas (Done doc) = pure (Done doc)
  expandMetas EqualTerm{ctx,ty,lhs,rhs} = do
    ctx' <- expandMetas ctx
    ty'  <- expandMetas ty
    lhs' <- expandMetas lhs
    rhs' <- expandMetas rhs
    return EqualTerm{ctx=ctx',ty=ty',lhs=lhs',rhs=rhs'}
  expandMetas EqualHeadTerm{ctx,ty,lhsV,rhsV} = do
    ctx'  <- expandMetas ctx
    ty'   <- expandMetas ty
    lhsV' <- traverse expandMetas lhsV
    rhsV' <- traverse expandMetas rhsV
    return EqualHeadTerm{ctx=ctx',ty=ty',lhsV=lhsV',rhsV=rhsV'}
  expandMetas EtaExpandMeta{mv,tel,endTy} = do
    mv'    <- {- expandMetas -} pure mv
    tel'   <- expandMetas tel
    endTy' <- expandMetas endTy
    return EtaExpandMeta{mv=mv',tel=tel',endTy=endTy'}

instance ExpandGuards (C t) where
  expandGuards (Done doc) = pure (Done doc)
  expandGuards EqualTerm{ctx,ty,lhs,rhs} = do
    ctx' <- traverse expandGuards ctx
    ty'  <- expandGuards ty
    lhs' <- pure lhs
    rhs' <- pure rhs
    return EqualTerm{ctx=ctx',ty=ty',lhs=lhs',rhs=rhs'}
  expandGuards EqualHeadTerm{ctx,ty,lhsV,rhsV} = do
    ctx'  <- traverse expandGuards ctx
    ty'   <- expandGuards ty
    lhsV' <- pure lhsV
    rhsV' <- pure rhsV
    return EqualHeadTerm{ctx=ctx',ty=ty',lhsV=lhsV',rhsV=rhsV'}
  expandGuards c@EtaExpandMeta{} = pure c

refineEqualTerm :: Unify t => CtxTC t -> TwinTypeC t -> Term t -> Term t -> UFR t
refineEqualTerm ctx ty t1 t2 =
       readConf <&> confNfInUnifier >>= \case
         False -> tryMetaWhnf  t1 t2
         True  -> tryWhnf      t1 t2
  where
    tryMetaWhnf t1 t2 = do
      -- Ensure that λ abstractions are not masking constraints
      -- headed by the same meta.
      blockedT1 <- whnfMeta =<< etaContract t1
      blockedT2 <- whnfMeta =<< etaContract t2
      case (blockedT1, blockedT2) of
        (MetaBlockingHead mv1 elims1, MetaBlockingHead mv2 elims2) ->
          doubleMetaAssign ctx ty mv1 elims1 mv2 elims2
        (MetaBlockingHead mv1 elims1, _) -> metaAssignOrBlock ctx ty mv1 elims1 =<< ignoreMetaBlocking_ blockedT2
        (_, MetaBlockingHead mv2 elims2) -> metaAssignOrBlock (flipTT ctx) (flipTT ty) mv2 elims2 =<< ignoreMetaBlocking_ blockedT1
        (MetaNotBlocked t1₂, MetaNotBlocked t2₂) -> tryWhnf t1₂ t2₂

    tryWhnf t1₂ t2₂ = do
      t1₃ <- etaContract =<< whnfTerm t1₂
      t2₃ <- etaContract =<< whnfTerm t2₂

      blockedT1 <- whnf t1₃
      blockedT2 <- whnf t2₃
      case (blockedT1, blockedT2) of
        (NotBlocked t1₄, NotBlocked t2₄) -> do
          -- Both sides in WHNF. Attempt to simplify the constraint.
          -- This includes when the head is a definition or postulate.
          t1v <- view t1₄
          t2v <- view t2₄
          refineHeadEqualTerm ctx ty t1v t2v

        (BlockingHeadMeta mv1 elims1, BlockingHeadMeta mv2 elims2) ->
          doubleMetaAssign ctx ty mv1 elims1 mv2 elims2
        (BlockingHeadMeta mv1 elims1, _) ->
          metaAssignOrBlock ctx ty mv1 elims1 =<< ignoreBlocking blockedT2
        (_, BlockingHeadMeta mv2 elims2) -> metaAssignOrBlock (flipTT ctx) (flipTT ty) mv2 elims2 =<< ignoreBlocking blockedT1

        (BlockedOn mvs f elims, _) ->
          refineTryInvertOrBlock (anyMeta mvs) ctx          ty          (f, elims) =<< ignoreBlocking blockedT2
           `elseTry` conversion
             `else_` postpone

        (_, BlockedOn mvs f elims) ->
          refineTryInvertOrBlock (anyMeta mvs) (flipTT ctx) (flipTT ty) (f, elims) =<< ignoreBlocking blockedT1
           `elseTry` conversion
             `else_` postpone

        (b1, b2) -> do
          
          t1' <- ignoreBlocking b1
          t2' <- ignoreBlocking b2
          conversion (getBlocker$ blockOr$ onBlocked b1 >> onBlocked b2) CheckEqualTerm{ctx,ty,lhs=t1',rhs=t2'}
            `else_` postpone

-- | Tries to convert both terms using δ-expansion, and,
--   η-contraction.
conversion :: IsTerm t => Blockers -> CheckEqualTerm t -> UFRE t
conversion bs CheckEqualTerm{ctx,ty,lhs,rhs} =
  --weakNfFromConf $ \weakNf ->
  convertibleOrBlock whnf ctx lhs rhs >>= \case
    Convertible           -> progress =<< done
    PerhapsConvertible b3 -> goOn (bs \/ blockersOn b3) CheckEqualTerm{ctx=ctx,ty=ty,lhs=lhs,rhs=rhs}

type UFRE t = UFW t (Either (Blockers, CheckEqualTerm t) (Cs t))

progress :: Cs t -> UFRE t
progress = pure . Right 

goOn :: Blockers -> CheckEqualTerm t -> UFRE t
goOn = curry$ pure . Left 

elseTry :: UFRE t ->
           (Blockers -> CheckEqualTerm t -> UFRE t) ->
           UFRE t
elseTry m f = do
  m >>= \case
    Right cs -> return$ Right cs
    Left (bs,ce) -> f bs ce

else_ :: UFRE t ->
           (Blockers -> CheckEqualTerm t -> UFR t) ->
           UFR t
else_ m f = do
  m >>= \case
    Right cs -> return cs
    Left (bs,ce) -> f bs ce

postpone :: Unify t => Blockers -> CheckEqualTerm t -> UFR t
postpone bs CheckEqualTerm{ctx,ty,lhs,rhs} =
  newBlockedConstraint bs EqualTerm{ctx,ty,lhs,rhs}

----------------------------------------
-- Fallback                           --
----------------------------------------

infixl 0 `elseTry`
infixl 0 `else_`

data MetaAssignResult t where
  AssignSuccess  :: Cs t
                 -> MetaAssignResult t
  AssignWait     :: Blockers
                    --   Blockers that must be solved before the meta assignment can proceed.
                    --   This will presumably include the meta itself.
                 -> CheckEqualTerm t
                    --   Simplified term. The meta assignment might have caused some pruning to take place.
                 -> MetaAssignResult t

metaAssignOrBlock :: Unify t => CtxTC t -> TwinTypeC t -> Meta -> Elims t -> Term t -> UFR t
metaAssignOrBlock ctx ty m es t = metaAssign ctx ty m es t >>= \case
  AssignSuccess cs -> return cs
  AssignWait bs (CheckEqualTerm {ctx,ty,lhs,rhs}) ->
    newBlockedConstraint bs EqualTerm{ctx,ty,lhs,rhs}

doubleMetaAssign :: Unify t => CtxTC t -> TwinTypeC t -> Meta -> Elims t -> Meta -> Elims t -> UFR t
doubleMetaAssign ctx ty mv1 elims1 mv2 elims2
  | mv1 == mv2 = sameMeta ctx ty mv1 elims1 elims2
  | (Down$ length elims1, mv1) < (Down$ length elims2, mv2) =
      doubleMetaAssign' ctx ty mv1 elims1 mv2 elims2
  | otherwise =
      doubleMetaAssign' (flipTT ctx) (flipTT ty) mv2 elims2 mv1 elims1


doubleMetaAssign' :: Unify t => CtxTC t -> TwinTypeC t -> Meta -> Elims t -> Meta -> Elims t -> UFR t
doubleMetaAssign' ctx ty mv1 elims1 mv2 elims2 = do
  t2 <- meta mv2 elims2 
  metaAssign ctx ty mv1 elims1 t2 >>= \case
    AssignSuccess cs -> return cs
                           -- No point in trying the other direction,
                           -- as we will obtain the same `cs` even in the other
                           -- direction.
    AssignWait b1 CheckEqualTerm{ctx=ctx',lhs=lhs',rhs=rhs',ty=ty'} -> do
      whnfMeta rhs' >>= \case
        MetaBlockingHead mv2 elims2 -> metaAssign (flipTT ctx') (flipTT ty') mv2 elims2 lhs'  >>= \case
          AssignSuccess cs -> return cs
          AssignWait b2 CheckEqualTerm{ctx=ctx'',lhs=lhs'',rhs=rhs'',ty=ty''} ->
            newBlockedConstraint (b1 \/ b2) EqualTerm{ctx=ctx'',ty=ty'',lhs=lhs'',rhs=rhs''}
        MetaNotBlocked rhs'' -> do
          b2 <- isBlocked <$> whnf rhs''
          newBlockedConstraint (b1 \/ anyMeta (fromMaybe bottom b2)) EqualTerm{ctx=ctx',ty=ty',lhs=lhs',rhs=rhs''}

---------------------------------------------
-- Intersection                            --
---------------------------------------------
sameMeta :: Unify t => CtxTC t -> TwinTypeC t -> Meta -> Elims t -> Elims t -> UFR t
sameMeta ctx ty mv es1 es2 = do
  let fallback bs = do
        lhs <- meta mv es1 
        rhs <- meta mv es2
        newBlockedConstraint (bs \/ (anyMeta$ metaGuard mv)) EqualTerm{ctx,ty,lhs,rhs}  

  
  --       - Support killing projection and even record arguments.
  --         (e.g. the variable cannot depend on those fields that do not
  --          agree).
  intersectMetaSpine ctx mv es1 es2 >>= \case
    Nothing  -> done
    Just mvs -> fallback (anyMeta mvs)

intersectMetaSpine :: (IsTerm t) => Ctx α -> Meta -> [Elim t] -> [Elim t] -> TC t r s (Maybe Guard)
intersectMetaSpine ctx mv els1 els2 = do
  let msg = runNamesT ctx$ do
        els1Doc <- prettyM els1
        els2Doc <- prettyM els2
        return $
          "metavar:" <+> PP.pretty mv $$
          "elims 1:" //> els1Doc $$
          "elims 2:" //> els2Doc
  debugBracket DL.IntersectMetaSpine msg $ do
      mbKills <- intersectVars els1 els2
      debug_ "kills:" $ PP.pretty mbKills
      case mbKills of
        Nothing ->
          
          pure$ Just$ metaGuard mv
        Just kills -> do
          mvType <- getMetaType mv
          (mvType', kills') <- createNewMetaFromKills mvType kills
          when (any unNamed kills') $ do
            debug_ "new kills:" $ PP.pretty kills'
            newMv <- addMeta mvType'
            unsafeInstantiateMeta mv =<< killArgs newMv kills'
          -- If we were able to perform all the kills, then the constraint became trivial.
          -- Otherwise, we need to wait until the constraint becomes solvable again.
          if map unNamed kills' == kills then
            return Nothing
          else
            pure$ Just$ metaGuard mv

data TwinWhnfView t = Whnf (TermView (TwinType t))
                    | WhnfBlocked Blockers (TwinTypeC t)
                    | HeadNotEqual
{-# INLINE twinWhnfViewType #-}
-- | Obtains the WHNF of a twin pair of types.
--   Note that, unless either one of the types is blocked,
--   the heads of the types must match.
twinWhnfViewType :: IsTerm t => TwinTypeC t -> UFW t (TwinWhnfView t)
twinWhnfViewType (SingleT t) = do
  t' <- whnf t
  t'' <- ignoreBlocking t'
  case isBlocked t' of
    Nothing -> Whnf . fmap SingleT <$> view t''
    Just bs -> return$ WhnfBlocked (anyMeta bs) (SingleT t'')

twinWhnfViewType TwinT{lty,rty,constraint,necessary} = do
    lty' <- whnf lty
    case isBlocked lty' of
      Just b1 -> do
        lty'' <- ignoreBlocking lty'
        return$ WhnfBlocked (anyMeta b1) TwinT{lty=lty'',rty,constraint,necessary}
      Nothing -> do
        rty' <- whnf rty
        case isBlocked rty' of
          Just b2 -> do
            lty'' <- ignoreBlocking lty'
            rty'' <- ignoreBlocking rty'
            return$ WhnfBlocked (anyMeta b2) TwinT{lty=lty'',rty=rty'',constraint,necessary}
          Nothing -> do
            lty'' <- view <=< ignoreBlocking $ lty' 
            rty'' <- view <=< ignoreBlocking $ rty' 
            case (lty'', rty'') of
              (Pi a1 (Abs name1 b1), Pi a2 (Abs name2 b2)) ->
                return $ Whnf $ Pi TwinT{lty=a1,rty=a2,constraint,necessary=()}
                   (Abs (name1 <> name2) TwinT{lty=b1,rty=b2,constraint,necessary=()})
              (App h1 pars1, App h2 pars2) | length pars1 == length pars2 -> do
                case commuteTT (TwinT h1 h2 constraint ()) of
                  Just h -> 
                    return$ Whnf$ App h
                      [ Apply$ TwinT{lty=p1,rty=p2,constraint,necessary=()} 
                      | (Apply p1, Apply p2) <- zip pars1 pars2
                      ]
                  Nothing -> return HeadNotEqual
              (Equal a1 x1 y1, Equal a2 x2 y2) ->
                return$ Whnf (Equal (TwinT a1 a2 constraint ())
                                    (TwinT x1 x2 constraint ())
                                    (TwinT y1 y2 constraint ()))
              (Set, Set) -> return$ Whnf Set
              _          -> return HeadNotEqual
               


-- | Infers the (twin) type of a head.
--   For variables, there might actually be two types.
inferTwinType
  :: forall t. (IsTerm t)
  => CtxTC t -> Head t -> UFW t (TwinTypeC t)
inferTwinType ctx h = case h of
  Var v      -> coerce <$> ctxGetVar v (coerce ctx :: CtxTC (OpenTerm t))
  Def name   -> SingleT <$> (definitionType =<< getDefinition name)
  Meta mv    -> SingleT <$> getMetaType mv
  J          -> return$ SingleT typeOfJ
  Twin{}     -> __IMPOSSIBLE__ -- We are not actually using twins

mkSpineHead :: IsTerm t => CtxTC t -> Head t -> UFW t (TwinTerm t :∈ TwinType t)
mkSpineHead ctx h = (:∈) <$> (SingleT <$> app h []) <*> (forgetN <$> inferTwinType ctx h)

updateTwin :: TwinTypeC a -> Type t -> Type t -> TwinTypeC t
updateTwin TwinT{constraint,necessary} lty rty = TwinT{constraint,necessary,lty,rty}

data IsNotSingletonTypeTwin t =
          IsNotSingletonTypeTwinBlocked Blockers (TwinTypeC t)
        | IsSingletonTypeTwin               (TwinTypeC t :∋ Either t t)
        | IsSingletonTypeTwinBoth           (TwinTypeC t :∋ t)
        | IsNotSingletonTypeTwin

isNotSingletonTypeTwin :: forall t. (Unify t) => TwinTypeC t -> UFW t (IsNotSingletonTypeTwin t)
isNotSingletonTypeTwin (SingleT ty) =
  isNotSingletonType ty >>= \case
    IsNotSingletonType                -> return$ IsNotSingletonTypeTwin
    IsSingletonType  (ty' :∋ s)       -> return$ IsSingletonTypeTwinBoth (SingleT ty' :∋ s)
    IsNotSingletonTypeBlocked bs ty'  -> return$ IsNotSingletonTypeTwinBlocked bs (SingleT ty')

-- Remarks:
--  - If one side is of singleton type, the other one will be either blocked
--    or of singleton type. So we might as well give up.
--  - If one side is of non-singleton type, the other side will also be of
--    non-singleton type in any solution. Therefore, it's a success.
isNotSingletonTypeTwin tw@TwinT{constraint,necessary,lty,rty} =
  isNotSingletonType lty >>= \case
    IsNotSingletonType -> return IsNotSingletonTypeTwin
    IsSingletonType (lty' :∋ s)       -> return$ IsSingletonTypeTwin
                                                   (updateTwin tw lty' rty :∋ Left s)
    IsNotSingletonTypeBlocked lbs lty' ->
      isNotSingletonType rty >>= \case
        IsNotSingletonType -> return IsNotSingletonTypeTwin
        IsSingletonType (rty' :∋ s)        -> return$ IsSingletonTypeTwin
                                                       (updateTwin tw lty' rty' :∋ Right s)
        IsNotSingletonTypeBlocked rbs rty' -> return$ IsNotSingletonTypeTwinBlocked (lbs \/ rbs) (updateTwin tw lty' rty')

data IsNotSingletonType t =
          IsNotSingletonTypeBlocked Blockers (Type t)
        | IsSingletonType (Type t :∋ Term t)
        | IsNotSingletonType

getProjectionType :: MonadTerm t m => Opened Projection t -> [Term t] -> m (Type t)
getProjectionType proj args = do
  let projName = first pName proj
  getDefinition projName >>= \case
    Projection _ _ ty -> do
      appliedProjType <- openContextual ty args
      appliedProjTypeView <- whnfView appliedProjType
      case appliedProjTypeView of
        Pi _ endType -> return$ unAbs$ endType
        _ -> __IMPOSSIBLE__
    _ -> __IMPOSSIBLE__
--  getDefinition (first pName proj)

isNotSingletonType :: forall t. (Unify t) => Type t -> UFW t (IsNotSingletonType (Type t))
isNotSingletonType ty = do
    whnfViewOrBlockers ty >>= \case
      Left  (bs, ty') -> return$ IsNotSingletonTypeBlocked bs ty'
      Right (ty',vty) ->
        case vty of
          Pi a (Abs{absName,unAbs=b}) ->
            isNotSingletonType b >>= \case

              IsNotSingletonTypeBlocked bs b'  -> do
                ty'' <- pi a Abs{absName,unAbs=b'}
                return$ IsNotSingletonTypeBlocked bs ty''

              IsSingletonType (b' :∋ sb) -> do
                ty'' <- pi a Abs{absName,unAbs=b'}
                s    <- lam Abs{absName,unAbs=sb}
                return$ IsSingletonType (s :∈ ty'')

              IsNotSingletonType  -> return IsNotSingletonType

          Set               -> return IsNotSingletonType
          Lam{}            -> __IMPOSSIBLE__
          Equal{}          -> __IMPOSSIBLE__
          Refl             -> __IMPOSSIBLE__
          Con _conName _ts -> __IMPOSSIBLE__ 
          App (Def (OTyCon tyCon)) es  -> do
            let args = fromMaybe __IMPOSSIBLE__ (mapM isApply es)
            getDefinition tyCon >>= \case
              Constant _ (Record dataCon projs) ->
                let check :: Seq (Either Blockers (Term t)) -> [_] -> _
                    check sbs [] = do
                      case partitionEithers (toList sbs) of
                        ([], ss) -> do
                          s <- con dataCon ss
                          return$ IsSingletonType (ty' :∋ s)
                        (bs, _) -> do
                          return$ IsNotSingletonTypeBlocked (joins bs) ty'
                    check sbs (proj:ps) = do
                          pty <- getProjectionType proj args
                          isNotSingletonType pty >>= \case
                            IsNotSingletonTypeBlocked bs _ -> check (sbs :|> Left bs) ps
                            IsSingletonType (s :∈ _)  -> check (sbs :|> Right s) ps
                            IsNotSingletonType -> return IsNotSingletonType
                in
                check [] projs
              Constant _ (Data{}) -> return IsNotSingletonType
              Constant _ (Function{}) -> __IMPOSSIBLE__
          -- If it's stuck, then it's not of singleton type
          App (Def (OFDef  _name)) _es  -> return IsNotSingletonType
          App (Def (OPDef  _name)) _es  -> return IsNotSingletonType
          App _ _es              -> return IsNotSingletonType

-- | Simplifies a constraint where both sides and the type are in WHNF.
refineHeadEqualTerm :: Unify t => CtxTC t -> TwinTypeC t -> TermView t -> TermView t -> UFR t
refineHeadEqualTerm ctx ty = goApp
  where
    goApp t1 t2 = do
      t1' <- etaExpandDefHeaded t1
      t2' <- etaExpandDefHeaded t2
      let fallback = goRest t1' t2'
      case (t1', t2') of
        (App h1 elims1, App h2 elims2) -> do
          mkSynEq h1 h2 >>= \case
            Just h -> do
              
              mbH <- mkSpineHead ctx h
              refineEqualStrongNeutral ctx ty mbH elims1 elims2
            Nothing ->
              -- A mismatched head does not automatically imply that the constraints cannot
              -- be unified.
              --
              -- For example:
              --
              -- postulate A : Set
              -- 
              -- f : A -> A
              -- f x = x
              -- 
              -- g : A -> A
              -- g x = x
              -- 
              -- testEq : f == g
              -- testEq = refl
              fallback
              
        _ -> fallback

    goRest t1 t2 =
      twinWhnfViewType ty >>= \case
        HeadNotEqual        -> newBlockedConstraint Bottom $ EqualHeadTerm ctx ty t1 t2 -- cannotSolve "Mismatched head type"
        WhnfBlocked bs ty'  -> newBlockedConstraint bs $ EqualHeadTerm ctx ty' t1 t2 
        Whnf ty'            -> do

          t1' <- etaExpand (t1 :∈ fmap twinLeft  ty')
          t2' <- etaExpand (t2 :∈ fmap twinRight ty')

          let block bs = do
                            ty'' <- traverse unview $ traverse id ty'
                            newBlockedConstraint bs $ EqualHeadTerm ctx (embedN ty'') t1' t2'
          case (t1', t2') :∈ ty' of
            -- 
            (Lam (Abs_ body1), Lam (Abs_ body2)) :∈ Pi dom (Abs name cod) -> do
              ctx'  <- extendContext  ctx (name, embedN dom)
              -- Twins variables are not actually needed, because they are only
              -- ever introduced in their corresponding side of the equation,
              -- and terms do not move from one side of the equation to the other.
              {- v1 <- twin Fst v; body1' <- applySubst body1 (subFromList$ B0 :. v1)
              v2 <- twin Snd v; body2' <- applySubst body1 (subFromList$ B0 :. v2) -}
              refineEqualTerm ctx' (embedN cod) body1 body2

            (Con dataCon1 dataConArgs1,
             Con dataCon2 dataConArgs2) :∈
             App _        tyConPars -> do

              mkSynEq dataCon1 dataCon2 >>= \case
                Just dataCon -> do 
                  let Just tyConPars' = mapM isApply tyConPars
                  DataCon _ _ dataConType <- getDefinition dataCon
                  appliedDataConType <- traverse (openContextual dataConType) $ sequenceA tyConPars'
                  refineEqualSpine ctx (Nothing :∈ appliedDataConType) (map Apply dataConArgs1) (map Apply dataConArgs2)
                Nothing -> block Bottom -- cannotSolve "Mismatched data constructor"

            (Pi dom1 (Abs name1 cod1), Pi dom2 (Abs name2 cod2)) :∈ Set ->
               watching (newConstraint EqualTerm{ctx,lhs=dom1,rhs=dom2,ty=SingleT set}) $ \cty ->
                  let ctx' = ctx :< (name1 <> name2, TwinT{lty=dom1,rty=dom2,constraint=cty,necessary=True}) in
                  newConstraint EqualTerm{ctx=ctx',lhs=cod1,rhs=cod2,ty=SingleT set}

            (Equal type1' l1 r1, Equal type2' l2 r2) :∈ Set ->
               watching (newConstraint EqualTerm{ctx,lhs=type1',rhs=type2',ty=SingleT set}) $ \cty ->
                  let ty = TwinT{lty=type1',rty=type2',constraint=cty,necessary=True} in
                  (/\) <$> newConstraint EqualTerm{ctx,lhs=l1,rhs=l2,ty}
                       <*> newConstraint EqualTerm{ctx,lhs=r1,rhs=r2,ty}

            (Set, Set) :∈ Set -> done

            (Refl, Refl) :∈ Equal{} -> done

            (_,_) :∈ _ -> cannotSolve "Mismatch between term and type"


-- | @etaExpand A t@ η-expands term @t@.
etaExpand :: forall t r s. (IsTerm t) => (TermView t :∋ TermView t) -> TC t r s (TermView t)
etaExpand (tView :∈ typeView) = do
    let fallback = return tView
    case typeView of
      App (Def tyCon) _ -> do
        tyConDef <- getDefinition tyCon
        case tyConDef of
          Constant _ (Record dataCon projs) -> do
            case tView of
              -- Optimization: if it's already of the right shape, do nothing
              Con _ _ -> do
                fallback
              _ -> do
                t  <- unview tView
                ts <- sequence [eliminate t [Proj p] | Opened p _ <- projs]
                return$ Con (first conName dataCon) ts
          _ -> do
            fallback
      Pi _ cod -> do
        name <- getAbsName_ cod
        v <- var $ boundVar name
        -- Expand only if it's not a λ-function
        case tView of
          Lam _ -> return tView
          _ -> do
            t' <- weaken_ 1 =<< unview tView
            Lam . Abs name <$> eliminate t' [Apply v]
      _ -> return tView

mkSynEq :: (MonadTerm t m, SynEq t a) => a -> a -> m (Maybe a)
mkSynEq p q = synEq p q >>= \case
  True  -> return$ Just p
  False -> return  Nothing

refineEqualStrongNeutral ::
  forall t. Unify t => CtxTC t -> TwinTypeC t -> TwinTerm t :∈ TwinType t -> Elims t -> Elims t -> UFR t
refineEqualStrongNeutral ctx twty mbH@(h :∈ hty) elims1 elims2 =
  let msg = runNamesT ctx$ do
        ctxDoc <- prettyM ctx
        tyDoc <- prettyM twty
        hDoc <- prettyM mbH
        elims1Doc <- prettyM elims1
        elims2Doc <- prettyM elims2
        return $
          "ctx:" //> ctxDoc $$
          "ty:"  //> tyDoc $$
          "head:" //> hDoc $$
          "elims1:" //> elims1Doc $$
          "elims2:" //> elims2Doc
  in
  debugBracket DL.CheckEqualSpine msg $
    -- Check if it's singleton type
    isNotSingletonTypeTwin twty >>= \case
      IsNotSingletonTypeTwinBlocked bs twty' ->
        newBlockedConstraint bs EqualStrongNeutral{ctx,ty=twty',mbH,elims1,elims2}
      IsSingletonTypeTwin (twty' :∋ Left lhs) -> do
        rhs <- eliminate (twinRight h) elims2 
        newConstraint EqualTerm{ctx,ty=twty',lhs,rhs}
      IsSingletonTypeTwin (twty' :∋ Right rhs) ->  do
        lhs <- eliminate (twinLeft h) elims2 
        newConstraint EqualTerm{ctx,ty=twty',lhs,rhs}
      IsSingletonTypeTwinBoth{}  -> done
      IsNotSingletonTypeTwin ->
        refineEqualSpine ctx (Just h :∈ hty) elims1 elims2

-- | Unifies a series of eliminators.
refineEqualSpine :: forall t. Unify t => CtxTC t -> Maybe (TwinTerm t) :∈ TwinType t -> Elims t -> Elims t -> UFR t
refineEqualSpine ctx mbH elims1 elims2 =
  let msg = runNamesT ctx$ do
        ctxDoc <- prettyM ctx
        hDoc <- prettyM mbH
        elims1Doc <- prettyM elims1
        elims2Doc <- prettyM elims2
        return $
          "ctx:" //> ctxDoc $$
          "ty:"  //> ctxDoc $$
          "head:" //> hDoc $$
          "elims1:" //> elims1Doc $$
          "elims2:" //> elims2Doc
  in
  debugBracket DL.CheckEqualSpine msg $
    go ctx mbH elims1 elims2
  where
    go :: CtxTC t -> Maybe (TwinTerm t) :∈ TwinType t -> Elims t -> Elims t -> UFR t
    go _ _ [] [] = done
    go ctx (h :∈ ty) es1 es2 = do

      twinWhnfViewType (embedN ty) >>= \case
        HeadNotEqual -> cannotSolve "Mismatched twin type"
        Whnf (Pi dom cod) -> case (es1, es2) of
          
          -- this case, the head is not needed any longer and could be discarded.
          (Apply x:es1', Apply y:es2') -> do
            watching (newConstraint EqualTerm{ctx,lhs=x,rhs=y,ty=embedN dom}) $ \carg -> do
              let arg = TwinT x y carg ()
              debug "argument: "$ runNamesT ctx$ prettyM arg
              cod' <- sequence$ instantiate_ <$> (sequenceA cod) <*> arg
              debug "new codomain: "$ runNamesT ctx$ prettyM cod'
              h' <- forM h (\t -> sequence$ eliminate <$> t <*> ((:[]) . Apply <$> arg))
              go ctx (h' :∈ cod') es1' es2'
          (_,_) -> cannotSolve "Non-apply elimination of Π type"

        Whnf (App (Def (OTyCon tyCon)) (tyArgs)) -> case (es1,es2) of
          (Proj p:es1', Proj q:es2') -> do
            mkSynEq p q >>= \case
              Just p' -> do
                let Just h' = h
                ty' <- sequence$ applyProjectionType p' <$> h' <*> (sequenceA tyCon) <*> (sequenceA $ map sequenceA tyArgs)
                -- They are syntactically equal, so they are interreplaceable.
                h'' <- sequence$ flip eliminate [Proj p'] <$> h'
                go ctx (Just h'' :∈ ty') es1' es2'

              Nothing -> cannotSolve "Mismatched projections in left and right sides of spine."

          (_,_) -> cannotSolve "Non-projection elimination of record type" 

        Whnf _ -> cannotSolve "Wrong type of spine head"

        -- We do not know the type yet (although it is certain that we will be able to solve it)
        WhnfBlocked _bs _ty' -> cannotSolve "Type of head in spine is blocked, cannot determine if Π or record."
          --newBlockedConstraint Bottom EqualSpine{ctx,head=(h :∈ forgetN ty'),lhsE=es1,rhsE=es2}

instance PrettyM t (C t) where  
  prettyM = \case
    (Done constr) -> do
      doc <- prettyM constr
      return ("DONE:" <+> doc)
    EqualTerm{ctx,ty,lhs,rhs} -> localCtx ctx $ do
      ctxDoc <- prettyM ctx
      t1Doc  <- prettyM lhs
      t2Doc  <- prettyM rhs 
      tyDoc  <- prettyM ty
      return $ group $
        ctxDoc <+> "⊢" //
        group (t1Doc //> hang 2 "=" //> t2Doc // "∈" // tyDoc)

    EqualHeadTerm{ctx,ty,lhsV,rhsV} -> localCtx ctx $ do
      ctxDoc <- prettyM_ ctx
      t1Doc  <- prettyM lhsV
      tyDoc <- prettyM ty
      t2Doc  <- prettyM rhsV
      return $ group $
        ctxDoc <+> "⊢" //
        group (t1Doc //> hang 2 "=c" //> t2Doc // "∈" // tyDoc)

    EtaExpandMeta{mv,tel,endTy} -> localCtx C0$ do
      mvDoc <- prettyM mv
      telDoc <- prettyM tel
      endTyDoc <- prettyM endTy
      return $
        "EtaExpandMeta" $$
        "mv:" //> mvDoc $$
        "tel:" //> telDoc $$
        "endTy:" //> endTyDoc

-- | Just give up if there are projections in the metavariable arguments.
trivialRemoveProjectionsT
  :: forall t.
     (IsTerm t)
  => CtxTC t -> [MetaArg' t]
  -> UFW t (Either Blockers (CtxTC t, [MetaArg t Var], Subst t))
trivialRemoveProjectionsT ctx args =
  pure$ case traverse (traverse (\case
                         (v,[]) -> pure v
                         _      -> Nothing)) args of
    Nothing    -> Left bottom
    Just args' -> Right (ctx, args', subId)

----------------------------------------
-- Remove projections                 --
----------------------------------------
-- | Remove projections from the arguments of a metavariable
--
--   It is understood that the meta arguments live on the
--   left side of the context.
removeProjectionsT
  :: forall t.
     (IsTerm t)
  => CtxTC t -> [MetaArg' t]
  -> UFW t (Either Blockers (CtxTC t, [MetaArg t Var], Subst t))
removeProjectionsT ctx0 mvArgs0 = do
    let msg = runNamesT ctx0$ do
          ctxDoc <- prettyM ctx0
          mvArgsDoc <- prettyM mvArgs0
          return $
            "ctx:" //> ctxDoc $$
            "args:" //> mvArgsDoc
    debugBracket DL.RemoveProjections msg $ runExceptT$ do
      (ctx, mvArgs, sub) <- go ctx0 mvArgs0
      return (ctx, mvArgs, twinRight sub)
  where
    go :: forall r. CtxTC t -> [MetaArg' t]
       -> ExceptT Blockers (UFW_ t r) (CtxTC t, [MetaArg t Var], TwinT (Subst t))
    go ctx [] = do
      return (ctx, [], pure subId)
    go ctx (MVAVar (v, []) : mvArgs) = do
      (ctx', mvArgs', tActs) <- go ctx mvArgs
      mvArg <- lift$ varApplyActions (twinLeft tActs) v
      return (ctx', mvArg : mvArgs', tActs)
    go ctx1 (MVAVar (v, (p : ps)) : mvArgs) = do
      (ctx2, tActs) <- ExceptT$ etaExpandContextVarT ctx1 v
      t <- (`eliminate` [Proj p]) =<< var v
      App (Var v') [] <- whnfView =<< applySubst t (twinLeft tActs)
      mvArgs' <- mapM (mvaApplyActions (twinLeft tActs)) mvArgs
      (ctx3, mvArgs'', tActs') <- go (telToCtx ctx2) (MVAVar (v', ps) : mvArgs')
      tActs'' <- sequenceA$ subCompose <$> tActs' <*> tActs
      return (ctx3, mvArgs'', tActs'')
    go ctx1 (MVARecord tyCon mvArgs1 : mvArgs2) = do
      (ctx2, mvArgs1', tActs1) <- go ctx1 mvArgs1
      (ctx3, mvArgs2', tActs2) <- go ctx2 mvArgs2
      tActs3 <- sequenceA$ subCompose <$> tActs2 <*> tActs1
      return (ctx3, MVARecord tyCon mvArgs1' : mvArgs2', tActs3)


-- | @etaExpandContextVar v Γ@.  Pre:
--
-- * @v@ is in scope in @Γ@
--
-- * If @Γ₁; v : A; Γ₂@, either @A = D t1 ⋯ tn@, where @D@ is a record
--   constructor, or @A@ is blocked.
--
-- Returns the context with @v@ η-expanded if @A@ isn't blocked, the
-- blocking metas if it is.
etaExpandContextVarT
  :: forall t. (IsTerm t)
  => CtxTC t -> Var
  -> UFW t (Either Blockers (TelTC t, TwinT (Subst t)))
etaExpandContextVarT ctx v = do
  let msg = do
        ctxDoc <- prettyM_ ctx
        return $
          "ctx:" //> ctxDoc $$
          "var:" //> PP.pretty v
  
  debugBracket DL.EtaExpandContextVar msg $ do
    let (ctx1, vType, tel2) = splitContext ctx v
    twinWhnfViewType vType >>= \case
      Whnf{} -> do
        -- If the heads are equal, the resulting substitutions and telescopes will be compatible, so
        -- we can commute them back.
        (pars, acts) <- fmap commuteTT$ sequence$ etaExpandVarT <$> (forgetN vType)
        -- Well typed, should be same length on both sides
        let Just pars' = commuteTT $ pars
        (tel2', acts') <- applySubstTelT acts (fmap forgetN tel2)
        
        -- by η-equivalent terms should not change things.
        return $ Right (ctx1 `telAppend` (fmap embedN$ pars' `telAppend` tel2'), acts')
      WhnfBlocked bs _  -> return$ Left bs
      HeadNotEqual      -> cannotSolve "Mismatched type for projected variable"
    
-- | Apply a (possibly twin) substitution to a telescope
applySubstTelT :: (MonadTerm t m, ApplySubst t a)
  => TwinT (Subst t)
  -> Tel (TwinT a)
  -> m (Tel (TwinT a), TwinT (Subst t))
applySubstTelT sub T0 = pure (T0, sub)
applySubstTelT sub ((n, type_) :> tel) = do
  type' <- sequence$ applySubst <$> type_ <*> sub
  let sub' = subLift 1 <$> sub
  (tel', sub'') <- applySubstTelT sub' tel 
  return ((n, type') :> tel', sub'')

-- | Expands a record-typed variable ranging over the given 'Tel',
-- returning a new telescope ranging over all the fields of the record
-- type and the old telescope with the variable substituted with a
-- constructed record, and a substitution for the old variable.
etaExpandVarT
  :: forall t r s. (IsTerm t)
  => Type t
  -- ^ The type of the variable we're expanding.
  -> TC t r s (Ctx t, Subst t)
etaExpandVarT type_ = do
  App (Def tyCon) tyConPars0 <- whnfView type_
  Constant _ (Record dataCon projs) <- getDefinition tyCon
  DataCon _ _ dataConType <- getDefinition dataCon
  let Just tyConPars = mapM isApply tyConPars0
  appliedDataConType <- openContextual dataConType tyConPars
  (dataConPars0, _) <- assert_ ("etaExpandVar, unrollPiWithNames:" <+>) $
    unrollPiWithNames appliedDataConType (map (qNameName . getQName . pName . opndKey) projs)
  let dataConPars = telToCtx dataConPars0
  dataConT <- con dataCon =<< mapM var (ctxVars dataConPars)
  
  -- specially like in metavar expansion?
  sub <- subInstantiate dataConT $ subWeaken (ctxLength dataConPars) subId
  return (dataConPars, sub)

----------------------------------------
-- Meta inversion                     --
----------------------------------------

metaAssign :: forall t r. Unify t => CtxTC t -> TwinTypeC t -> Meta -> Elims t -> Term t -> UFW_ t r (MetaAssignResult t)

-- This is the simplest problem possible.
metaAssign ctx@C0 ty@SingleT{} mv [] t2 = do
  safeInstantiateMeta_ mv (MetaBody 0 t2) >>= \case
    Left (gs, _) -> do
      t1 <- meta mv []
      return$ AssignWait (blockersOn gs) CheckEqualTerm{ctx,ty,lhs=t1,rhs=t2}
    Right{}      -> AssignSuccess <$> done

metaAssign ctx ty mv es t2 = do

  let fallback bs = do
        -- Prune the left side
        fvs <- fvAll <$> freeVars t2
        _ <- pruneMeta fvs mv es
        -- Carry on!
        t1 <- meta mv es 
        return$ AssignWait (anyMeta (metaGuard mv) \/ bs) CheckEqualTerm{ctx,ty,lhs=t1,rhs=t2}

  -- Before unifying twins, we check that this equation actually has hopes of being solved 
  -- The rationale is that twins will eventually be unified, but checking whether they unify manually is expensive.
  --
  -- IDEA: We can guard a constraint with a constraints that subsume it. If the guard is satisfied,
  -- then the constraint can be summarily discarded.
  -- This can save a lot of money when doing heterogeneous stuff.
  mvArgs <- checkMetaElims es
  case mvArgs of
    
    --       This opt may be redundant if we store the WHNF with the term.
    Failure (Meet bs) -> fallback bs
    Success args -> do
      paranoid <- confParanoidContextCurrying <$> readConf 
      (if paranoid then
         trivialRemoveProjectionsT ctx args
       else 
         removeProjectionsT ctx args) >>= \case -- removeProjectionsT ctx args >>= \case
        Left  bs    -> fallback bs
        Right (ctx', args', sub') -> do
          ty' <- applySubst (coerce ty :: TwinTypeC (OpenTerm t)) sub'
          t2' <- applySubst t2 sub'
          metaAssignArgs ctx' (coerce ty') mv args' t2'

metaAssignArgs :: forall t r. Unify t => CtxTC t -> TwinTypeC t -> Meta -> [MetaArg t Var] -> Term t -> UFW_ t r (MetaAssignResult t)
metaAssignArgs ctx ty mv args t2 = do
  let mvElimsM = mapM (fmap Apply . metaArgToTerm) args 
  let fallback bs t2' = do
        t1 <- meta mv =<< mvElimsM 
        return$ AssignWait (anyMeta (metaGuard mv) \/ bs) CheckEqualTerm{ctx,ty,lhs=t1,rhs=t2'}

  checkPatternCondition args >>= \case
    Nothing  -> do
      (t2I, t2g) <- runExpandMetas t2
      
      -- Simpler alternative: prune the meta, restart the equality
      fvs <- fvAll <$> freeVars t2I
      _ <- pruneMeta fvs mv =<< mapM (fmap Apply . metaArgToTerm) args
      fallback (anyMeta$ metasOnly t2g) t2I
      
      -- If these variables do not appear on the rhs, then the constraint can be solved
      -- anyway.
      --
      -- There is a fundamental distinction between linearity conflicts and free variables
      -- when it comes to pruning.
      --
      -- With linearity conflicts, we *want* the variable not to appear in the RHS in any position.
      -- With other free variables, we know it will not appear in any position.
      --
      -- For a more advanced implementation, the free
      -- variables function should say which metas/definitions could make
      -- which variables disappear. We could also normalize those parts of the term
      -- that contain these variables, as a last resort attempt.
      --
      -- The ideal would be to classify constraints according to the level of 'effort' required
      -- to solve them, and only solve low-effort constraints on a first pass, before
      -- switching to high-effort constraints.

    Just inv -> do

      -- Apply the substitution to the term now
      -- Or, if the free vars are easy to compute, we can check them and avoid pruning. 
      let allowedVars = B.fromList $ invertMetaVars inv
      t2I' <- -- If the meta arguments cover all the variables in the context,
             -- there is no need to prune.
             if allowedVars == B.fromList (ctxVars ctx) then
                evalExpandMetas t2
             else do
                t2I' <- prune allowedVars t2
                debug "pruned term" $ runNamesT ctx $ prettyM t2I'
                return t2I'

      applyInvertMeta ctx inv t2I' >>= \case
        Success mvb -> AssignSuccess <$> do
          -- Add constraints that will make the context equal when solved,
          -- and add those constraints to the context types.  
          refineEqualContext ctx $ \ctx' ->
            refineEqualTwinType ctx' ty $ \ty' -> do
              mvElims <- mvElimsM                                            
              perhapsDeferInstantiation ctx' ty' (mv,mvElims) (t2I',mvb)

        Failure (CCollect mvs) -> fallback (anyMeta$ metasGuard mvs) t2I'
        Failure (CFail _v)     -> fallback bottom t2I'
  where

perhapsDeferInstantiation :: Unify t
                   => CtxTC t 
                   -- ^ A refined context. That is, a context that
                   --   will simplify to a context without twin variables
                   --   iff both sides of the type of twin variable unify 
                   -> TwinTypeC t
                   -- ^ Type of both sides of the constraint
                   -> (Meta, Elims t)
                   -- ^ Metavariable and its eliminators. The metavariable is
                   --   assumed to be uninstantiated.
                   -> (Term t, MetaBody t)
                   -- ^ Term that is assigned to the meta variable and
                   --   its corresponding meta body.
                   -> UFR t
perhapsDeferInstantiation ctx ty (mv,lhsE) (rhs,mvb) = do
  rhs' <- evalExpandMetas rhs 
  let lhsM = meta mv lhsE
  checkHomogeneous ctx (((mv,lhsE),rhs') :∈ ty) $ \case
      (ctx',rhs'' :∈ ty',Top) -> safeInstantiateMeta_ mv mvb >>= \case
        Left (gs, _) -> do
          -- Occurs check failed. Block the constraint.
          lhs <- lhsM
          newBlockedConstraint (blockersOn gs) EqualTerm{ctx=ctx',ty=ty',lhs,rhs=rhs''}
        Right ()     -> done
      (ctx',rhs'' :∈ ty',bs)  -> do
        lhs <- lhsM
        newBlockedConstraint
           -- Unblock when either:
          (-- The context becomes homogeneous with respect to the rhs
              bs
           -- or, the metavariable being instantiated is instantiated somewhere else
           \/ anyMeta (metaGuard mv)
          ) EqualTerm{ctx=ctx',ty=ty',lhs,rhs=rhs''}

-- -- | Check if the context has a single type twin variables at the selected variables
-- --   Namely, those that are free on the left-hand side.
-- isUnifiedAt ::
--      VarSet
--      -- ^ Variables that we care about
--   -> CtxTC t
--       -- ^ Twin context
--   -> ConstraintGuard
-- isUnifiedAt fvs =   
--       ctxIndexed
--       -- Singulize those variables that do not occur in the given list
--   >>> foldMap (\(v,ty) -> Meet$ if v `B.member` fvs then constraintT ty else Top)
--   >>> getMeet
-- 
-- | Ensure that the two sides of a context unify, and
--   annotate each variable with the constraints that will ensure
--   that this will happen.
refineEqualContext :: forall t r. (Unify t)
  => CtxTC t
  -> (CtxTC t -> UFR_ t r)
  -- ^ 
  -> UFR_ t r
refineEqualContext = go
    where
      go :: CtxTC t -> (CtxTC t -> UFR_ t r) -> UFR_ t r
      go C0 κ = κ C0 
      go (ctx :< (name, ty)) κ =
        go ctx $ \ctx' ->
          refineEqualTwinType ctx' ty $ \ty' ->
            κ (ctx' :< (name,ty'))

refineEqualTwinType :: forall t r. Unify t => CtxTC t -> TwinTypeC t -> (TwinTypeC t -> UFR_ t r) -> UFR_ t r
refineEqualTwinType  ctx ty κ =
  ty & simplifyTT >>= \case
    ty'@SingleT{} -> κ ty'
    ty'@TwinT{necessary=True} -> κ ty'
    ty'@TwinT{constraint=Top} -> κ ty'
    TwinT{lty,rty} -> do
      lty' <- evalExpandMetas lty
      rty' <- evalExpandMetas rty
      mkSynEq lty' rty' >>= \case
        Nothing -> watching (newConstraint EqualTerm{ctx,lhs=lty',rhs=rty',ty=SingleT set}) $ \cid ->
          κ TwinT{lty,rty,constraint=cid,necessary=True}
        Just ty' -> κ (SingleT ty')

-- Check if a constraint is valid for assignment
-- Note that the meta side will always have more
-- free variables than the term side.
-- Because the important thing is that the variables that occur in
-- both (meta arguments and term) have unifiable types,
-- we only need to check the term.

-- Helper function
data Flexibilized t = Flexibilized GuardLattice t
instance FreeVars t a => FreeVars t (Flexibilized a) where
  freeVars (Flexibilized Bottom a) = freeVars a
  freeVars (Flexibilized _      a) = flexibilize <$> freeVars a
instance IsVarNotFree t a => IsVarNotFree t (Flexibilized a) where
  isVarNotFree_ (Flexibilized bs t) = censorJoin (Flexibly bs) $ Flexibilized bs <$> isVarNotFree_ t
instance PrettyM t a => PrettyM t (Flexibilized a) where
  prettyM (Flexibilized gs a) = do
    gsDoc <- prettyM gs
    aDoc  <- prettyM a
    pure$ "[" <+> gsDoc <+> "~" <+> aDoc <+> "]"

-- | Checks whether the two sides of the constraint are similar enough in
--   type that the metavariable can be instantiated.
checkHomogeneous :: forall t r. Unify t => CtxTC t -> ((Meta,Elims t),t) :∈ TwinTypeC t ->
                    ((CtxTC t, Term t :∈ TwinTypeC t, Blockers) -> UFR_ t r) -> UFR_ t r
checkHomogeneous ctx₀ (ty₀ :∋ (_mv, t₀)) κ = go
  where
    go = refineEqualTwinType ctx₀ ty₀ $ \ty' ->
      case constraintT ty' of
        Top -> do 
          ctx₁ <- simplifyTT ctx₀
          if isUnifiedTT ctx₁ then
            κ (ctx₁, t₀ :∈ ty', Top) 
          else
            let go' :: ICtxTC t -> Tel (Maybe (Flexibilized t)) -> (Term t :∈ _) -> _
                go' C0 _tel t_in_ty = κ (ctx₁, t_in_ty, Top)
                go' (ctx :< (name, (v', cty))) tel t_in_ty = do
                    (t_in_ty',bs1) <- isVarNotFree v'             t_in_ty
                    (tel',bs2)     <- isVarNotFree (mkVar name 0) tel
                    case (bs1 /\ bs2) of
                      DoesNotOccur ->
                        -- If the variable is not further used, it can be removed;
                        -- so it does not need to be further considered.
                        go' ctx ((name, Nothing) :> tel') t_in_ty'
                      Flexibly bsF ->
                        refineEqualTwinType (fmap snd ctx) cty $ \cty' ->
                          case constraintT cty' of
                            Top ->
                              -- If this variable appears in the term, we need to 
                              -- also take it's type into account when deciding 
                              -- whether to remove other variables.
                              -- However, we only care about the right side of the term.
                              -- Also, if the reason for the variable being free disappears (bsF),
                              -- this may warrant a recheck.
                              go' ctx ((name, Just$ Flexibilized bsF (twinRight cty')) :> tel') t_in_ty'
                            bsC -> 
                              -- If the type is not unified, we wait until either it becomes irrelevant,
                              -- or it unifies
                              κ (ctx₁, t_in_ty', blockersOn bsF \/ blockersOn bsC)
            in
            go' (ctxIndexed ctx₁) T0 (t₀ :∈ ty')
        bs  -> κ (ctx₀, t₀ :∈ ty', blockersOn bs) 

---------------------------------------------------------------------------
--                                                                       

--
--   - Sharing the unification constraints for the contexts of the later
--     parts.
--
--   or
--
--   - Making sure the constraint contexts and types have already the
--     necessary and sufficient constraints in their types.
--
--     Then it is just a matter of blocking on the required ones.
-- 
--     See notes for 2017-11-07
--
---------------------------------------------------------------------------

-- | if @checkMetaElims els ==> args@, @length els == length args@.
checkMetaElims
  :: (IsTerm t) => [Elim (Term t)]
  -> TC t r s (Validation (Meet Blockers) [MetaArg' t])
checkMetaElims elims = do
  case mapM isApply elims of
    Nothing   -> return $ Failure $ Meet $ bottom
    Just args -> sequenceA <$> mapM checkMetaArgWhnf args

-- | Check meta arguments 
--   For the meta to be invertible, we need all meta arguments to be of the right form.
checkMetaArg
  :: (IsTerm t) => Term t -> TC t r s (Validation (Meet Blockers) (MetaArg' t))
checkMetaArg arg = do
  blockedArg <- whnfMeta arg
  let fallback = return $ Failure $ Meet $ bottom
  case blockedArg of
    MetaNotBlocked t -> do
      etaContract t >>= viewW >>= \case
        App (Var v) vArgs -> do
          case mapM isProj vArgs of
            Just ps -> return $ pure $ MVAVar (v, ps)
            Nothing -> fallback
        Con dataCon recArgs -> do
          DataCon tyCon _ _ <- getDefinition dataCon
          isRecordType tyCon >>= \case
            True -> do
              recArgs'  <- sequenceA <$> mapM checkMetaArgWhnf recArgs
              return $ MVARecord tyCon <$> recArgs'
            False -> do
              fallback
        _ -> do
          fallback
    MetaBlockingHead mv _ -> do
      return $ Failure $ Meet $ anyMeta $ metaGuard mv

-- | Check meta arguments 
--   For the meta to be invertible, we need all meta arguments to be of the right form.
checkMetaArgWhnf
  :: (IsTerm t) => Term t -> TC t r s (Validation (Meet Blockers) (MetaArg' t))
checkMetaArgWhnf arg = do
  blockedArg <- whnf arg
  let fallback = return $ Failure $ Meet $ bottom
  case blockedArg of
    NotBlocked t -> do
      tView <- whnfView =<< etaContract t
      case tView of
        App (Var v) vArgs -> do
          case mapM isProj vArgs of
            Just ps -> return $ pure $ MVAVar (v, ps)
            Nothing -> fallback
        Con dataCon recArgs -> do
          DataCon tyCon _ _ <- getDefinition dataCon
          isRecordType tyCon >>= \case
            True -> do
              recArgs'  <- sequenceA <$> mapM checkMetaArgWhnf recArgs
              return $ MVARecord tyCon <$> recArgs'
            False -> do
              fallback
        _ -> do
          fallback
    BlockingHeadMeta mv _ -> do
      return $ Failure $ Meet $ anyMeta $ metaGuard mv
    BlockingHeadDef (Opened key _) _ -> do
      return $ Failure $ Meet $ anyMeta $ qNameGuard key
    BlockingHeadDef _ _ -> __IMPOSSIBLE__
    BlockedOn mvs _ _ -> do
      return $ Failure $ Meet $ anyMeta $ mvs

--------------------------------------------------------
-- Inversion                                          --
--------------------------------------------------------
refineTryInvertOrBlock
  :: forall t.
     (Unify t)
  => Blockers 
  -> CtxTC t
  -> TwinTypeC t
  -> (BlockedHead t, [Elim t])
  -> Term t
  -> UFRE t
refineTryInvertOrBlock bs ctx ty (bh, elims1) t2 = do
  let msg = runNamesT ctx$ do
        bhDoc <- prettyM bh
        mvsDoc <- prettyM bs
        return $ "Equality blocked on metavars" <+> mvsDoc <>
                  ", trying to invert definition" <+> bhDoc
  t1 <- ignoreBlockedOn bh elims1
  debugBracket DL.CheckEqualBlockedOn msg $ do
    case bh of
      BlockedOnJ -> do
        debug_ "head is J, couldn't invert." ""
        fallback t1
      BlockedOnFunction fun1 -> do
        Constant _ (Function (Inst clauses)) <- getDefinition fun1
        case clauses of
          NotInvertible _ -> do
            debug_ "couldn't invert." ""
            fallback t1
          Invertible injClauses -> do
            t2View <- whnfView t2
            let notInvertible = do
                  t2Head <- termHead t2
                  case t2Head of
                    Nothing -> do
                      debug_ "definition invertible but we don't have a clause head." ""
                      fallback t1
                    Just tHead | Just (Clause pats _) <- lookup tHead injClauses -> do
                      debug_ ("inverting on" <+> PP.pretty tHead) ""
                      -- Make the eliminators match the patterns
                      matched <- matchPats pats elims1
                      -- And restart, if we matched something.
                      if matched
                        then do
                          debug_ "matched constructor, restarting" ""
                          progress =<< newConstraint EqualTerm{ctx,ty,lhs=t1,rhs=t2}
                        else do
                          debug_ "couldn't match constructor" ""
                          fallback t1
                    Just _ -> do
                      cannotSolve =<< runNamesT ctx (do
                        t2Doc <- prettyM t2
                        fun1Doc  <- prettyM fun1
                        return$ "Head of" <+> t2Doc <+> "does not match definition of" <+> fun1Doc
                        )
            case t2View of
              App (Def fun2) elims2 -> do
                sameFun <- synEq fun1 fun2
                if sameFun
                  then do
                    debug_ "could invert, and same heads, checking spines." ""
                    mbH <- mkSpineHead ctx (Def fun1)
                    progress =<< refineEqualStrongNeutral ctx ty mbH elims1 elims2
                  else notInvertible
              _ -> do
                notInvertible
  where
    fallback t1 = goOn bs CheckEqualTerm{ctx,ty,lhs=t1,rhs=t2}

    matchPats :: [Pattern t] -> [Elim t] -> TC t r s Bool
    matchPats (VarP : pats) (_ : elims) = do
      matchPats pats elims
    matchPats (ConP dataCon pats' : pats) (elim : elims) = do
      matched <- matchPat dataCon pats' elim
      (matched ||) <$> matchPats pats elims
    matchPats _ _ = do
      -- Less patterns than arguments is fine.
      --
      -- Less arguments than patterns is fine too -- it happens if we
      -- are waiting on some metavar which doesn't head an eliminator.
      return False

    matchPat :: Opened DConName t -> [Pattern t] -> Elim t -> TC t r s Bool
    matchPat (Opened _ (_:_)) _ _ = do
      return False              
    matchPat openedDataCon@(Opened dataCon []) pats (Apply t) = do
      tView <- whnfView t
      case tView of
        App (Meta mv) mvArgs -> do
          mvT <- instantiateDataCon mv (DConName dataCon)
          void $ matchPat openedDataCon pats . Apply =<< eliminate mvT mvArgs
          return True
        Con (ODCon (Opened dataCon' _)) dataConArgs | dataCon == dataCon' -> do
          matchPats pats (map Apply dataConArgs)
        Con (ORCon{}) _ -> __IMPOSSIBLE__
        _ -> do
          -- This can happen -- when we are blocked on metavariables
          -- that are impeding other definitions.
          return False
    matchPat _ _ _ = do
      -- Same as above.
      return False

-- | Attempt to η-expand a meta.
--
--   This will, in particular, instantiate metavariables of unit type.
etaExpandMeta :: forall t. (Unify t) => Meta -> Tel t -> Type t -> UFR t
etaExpandMeta mv mvTel mvEndTy =
  let fallback bs mvTel' mvEndTy' =
         newBlockedConstraint (anyMeta (metaGuard mv) \/ bs)$ EtaExpandMeta mv mvTel' mvEndTy' 
  in
  -- 1. Check if the meta is already instantiated
  (flip sigMetaIsInstantiated mv <$> askSignature) >>= \case
    True  -> done
    False -> do
        -- 2. Try to further unroll the Π type
        (tel', endType') <- unrollPi mvEndTy
        let mvTel' = mvTel <> tel'
        whnfViewOrBlockers endType' >>= \case
          Left (bs, endType'') -> fallback bs mvTel' endType''
          Right (_, App (Def tyCon) tyConArgs0) -> 
            getDefinition tyCon >>= \case
              Constant _ Data{} ->
                    -- Data types cannot η-expand, end of discussion
                    done
              Constant _ (Record dataCon _) -> do
                    -- It’s a record! Let’s η-expand.
                    DataCon _ _ dataConType <- getDefinition dataCon
                    let Just tyConArgs = mapM isApply tyConArgs0
                    appliedDataConType <- openContextual dataConType tyConArgs
                    (dataConArgsTel, _) <- unrollPi appliedDataConType
                    dataConArgs <- createMvsPars (telToCtx mvTel') dataConArgsTel
                    mvT <- con dataCon dataConArgs
                    let mvb = MetaBody (telLength mvTel') mvT
                    unsafeInstantiateMeta mv mvb
                    done
                    -- If it’s a function a postulate, we want to wait to see if it gets instantiated in the end.
                    --
                    
                    -- If it is an actual postulate, we can give up now.
                    -- Note that it should be the WHNF function which tells us that it's blocked.
                    -- If we reach here, it is a bona-fide postulate.
              Constant _ Postulate{} ->
                    done
                    -- fallback (anyMeta$ qNameGuard (opndKey tyCon)) mvTel' endType''
                    -- If it is a function and it's in WHNF, it means that it will never reduce, so this will
                    -- never η-expand.
              Constant _ Function{} -> done

              DataCon{} -> __IMPOSSIBLE__
              Projection{} -> __IMPOSSIBLE__
              Module{} -> __IMPOSSIBLE__
          -- If the WHNF is not a type constructor or function application, this will never η-expand.
          Right _ -> done

weakNfFromConf :: (MonadConf m, MonadTerm t m) =>
  (forall a. BlockedTerm t a => (forall m. MonadTerm t m => t -> m a) -> m r) -> m r
weakNfFromConf κ = readConf <&> confNfInUnifier >>= \case
    True -> κ whnf
    False -> κ whnfMeta

-- ** Contingent booleans
newtype Convertible = CR GuardLattice
  deriving (MeetSemiLattice, JoinSemiLattice, BoundedMeetSemiLattice, BoundedJoinSemiLattice,DecBottom,DecTop)

deriving instance PrettyM t Convertible

-- | The meta does not occur
pattern Convertible        :: Convertible
pattern NotConvertible     :: Convertible
pattern PerhapsConvertible :: GuardLattice -> Convertible

pattern Convertible    = CR Top     -- does not occur
pattern NotConvertible = CR Bottom  -- occurs  

{-# COMPLETE Convertible,PerhapsConvertible #-}
pattern PerhapsConvertible bs  = CR bs      -- occurs, but perhaps not if …

-- | Note that one should not assume that both sides have the same type.
--   Also, η-convertibility does not apply to the unit type for this function.
--   This means that an unblocked, 'False' response just means that this function will never
--   return 'True', not that the terms might not be βδη-convertible in some contexts.
convertibleOrBlock :: forall a m t α. (MonadTerm t m, BlockedTerm t a, MonadConf m)
                       => (t -> m a)
                       -> Ctx α
                       -> Term t
                       -> Term t
                       -> m Convertible
                       -- ^ First argument: Are the terms convertible
                       -- ^ Second argument: Necessary condition for the terms to become convertible
convertibleOrBlock weakNf ctx₀ t1₀ t2₀ =
  let
      convertibleIf True  = pure$ Convertible
      convertibleIf False = pure$ NotConvertible
      
      goOpen :: IsQName qname => Opened qname t -> Opened qname t -> m Convertible
      goOpen (Opened key1 args1) (Opened key2 args2) =
        meetsM [convertibleIf$ key1 == key2
               ,convertibleIf$ length args1 == length args2
               ,meetsM [go arg1 arg2 | (arg1,arg2) <- zip args1 args2]   
               ]
      goOpen  _ _ = __IMPOSSIBLE__

      goHead (Var v1)   (Var v2)  = convertibleIf $ v1 == v2
      goHead  Var{}      _        = return NotConvertible
      goHead (Twin{})   (Twin{})  = __IMPOSSIBLE__
      goHead  Twin{}     _        = __IMPOSSIBLE__
      goHead (Meta m1)  (Meta m2) = convertibleIf $ m1 == m2 
      -- blocking already taken into account
      goHead  Meta{}     _        = return NotConvertible    
      goHead (Def d1)   (Def d2)  = goOpen d1 d2
      goHead  Def{}      _        = return NotConvertible
      goHead  J          J        = return Convertible
      goHead  J{}        _        = return NotConvertible

      goElim (Proj p1) (Proj p2)   = convertibleIf$ p1 == p2
      goElim Proj{}    _           = pure$ NotConvertible
      goElim (Apply t1) (Apply t2) = go t1 t2
      goElim Apply{}   _           = pure$ NotConvertible

      goView :: TermView t -> TermView t -> m Convertible
      goView = curry$ \case
       (Pi cod1 (Abs_ dom1), Pi cod2 (Abs_ dom2)) ->
         meetsM [go cod1 cod2
               ,go dom1 dom2
               ]
       (Equal a1 x1 y1, Equal a2 x2 y2) ->
         meetsM [go a1 a2
               ,go x1 x2
               ,go y1 y2
               ]
       (Set, Set)   -> return Convertible
       (Refl, Refl) -> return Convertible
       (Con con1 args1, Con con2 args2) ->
           meetsM [convertibleIf$ length args1 == length args2
                 ,goOpen con1 con2
                 ,meetsM [go arg1 arg2 | (arg1,arg2) <- zip args1 args2]
                ]
------   (Con ORCon{} _, _) -> tryEtaContract1
------   (_, Con ORCon{} _) -> tryEtaContract2
       (App def1 args1, App def2 args2) -> do
         meetsM [convertibleIf$ length args1 == length args2
               ,goHead def1 def2
               ,meetsM [goElim arg1 arg2 | (arg1,arg2) <- zip args1 args2]
               ]
       (Lam (Abs_ t1), Lam (Abs_ t2)) -> go t1 t2
------   (Lam{}, _) -> tryEtaContract1 -- η-contraction is always safe
------  (_, Lam{}) -> tryEtaContract2 -- η-contraction is always safe
       (_,_)      -> pure NotConvertible

      go :: t -> t -> m Convertible
      go t1 t2 =
        joinsM [
           convertibleIf =<< checkPhysEq_ t1 t2
           -- If the terms are convertible, we don't need to reconsider
           -- the result when more metas/definitions are instantiated,
           -- even if those definitions would change the normal form.
          ,do
              t1a <- weakNf t1; t1v <- ignoreBlocking_ t1a
              t2a <- weakNf t2; t2v <- ignoreBlocking_ t2a
              joinsM [goView t1v t2v
                     ,pure$ CR (maybe Bottom inj $ isBlocked t1a)
                     ,pure$ CR (maybe Bottom inj $ isBlocked t2a)
                     ]
          ]
  in 
    let msg = runNamesT ctx₀$ do
          t1Doc <- prettyM t1₀
          t2Doc <- prettyM t2₀
          return $
            "t1:" //> t1Doc $$
            "t2:" //> t2Doc
    in
    debugBracket DL.Conversion msg $ do
      res <- go t1₀ t2₀
      debug "convertible:" $ prettyM_ res
      return res

