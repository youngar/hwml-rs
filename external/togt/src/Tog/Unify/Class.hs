{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeInType #-}
{-# OPTIONS -Wno-partial-type-signatures #-}
{-# OPTIONS -Wno-duplicate-exports #-}
module Tog.Unify.Class (
  -- * Unifier class
    UnifierImpl(..), Unifier(..)
  , Constraints
  , SolveState(..)
  , UF, UF_
    -- * Blockers
  , Blockers
  , ConstraintGuard
  , anyMeta
  , allConstraints
  , BlockersOn(..)
  , done
  , cannotSolve
  , metaLattice
    -- * Shallow blocker toolkit
  , BlockerT, BlockerT_
  , blockWfView
  , blockAnd, blockOr, runBlockerT, blockOn
  , onBlocked
  , getBlocker
  , finalWhen
  , blockUnless
    -- * Re-exporting for convenience
  , module Algebra.Lattice
  , module Tog.Unify.Algebra
  , pattern FL.Top, pattern FL.Bottom
  , solve
  , initSolveState
  , module Tog.Unify.Core
  , whnfViewOrBlockers
  , whnfBlockers
  -- * Building constraints
  , newConstraint, newBlockedConstraint, sequenceConstraints
  -- * Introspection
  , getUnsolvedProblems
  , audit, auditState
  , isSolved, watching
  -- * Prettyprinting
  , ExpandGuards(..)
  , printSolveState
  ) where

import qualified Tog.Elaborate.Constraint     as Elaborate
import           Tog.Prelude
import qualified Tog.Unify.History as History
import           Tog.Unify.History (History')
import           Tog.Unify.Algebra
import           Tog.Unify.Core

import           Tog.Error
import           Tog.Instrumentation
import           Tog.Instrumentation.Timing (timingRaw)
import qualified Tog.Instrumentation.Debug.Label as DL

import           Tog.Term
import           Tog.Unify.Common (genericNfEq, Unify)
import           Tog.Names
import           Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import           Tog.Monad  (TC, askSrcLoc, ask, atSrcLoc, typeError, checkError)

import           Tog.PrettyPrint                  (($$), (//>), (<+>))
import qualified Tog.PrettyPrint                  as PP

import           Control.Lens ((<%=))
import           Data.Monoid (Any(..), Last(..))
import           Control.Monad (foldM)
import           Control.Monad.Reader (runReaderT, ReaderT, local)
import           Control.Monad.Writer.Strict (WriterT(..), mapWriterT)

import qualified Data.Kind as K
import qualified Data.ISet as IS

import Data.Refinement (Refinement)
import qualified Data.Refinement as R
import qualified Data.FreeLattice as FL
import Data.FreeLattice (FreeLattice)

import Algebra.Lattice hiding (join, meet)

import Data.Foldable (toList)
--import Development.Placeholders (notImplemented)

----------------------------------------------
-- Checking if constraints have been solved --
----------------------------------------------

newtype ConstraintGuard = ConstraintGuard { getConstraintGuard :: ISet ConstraintId } deriving (Eq)

instance        MeetSemiLattice ConstraintGuard where
  (/\) = (ConstraintGuard .) . IS.union `on` getConstraintGuard
instance BoundedMeetSemiLattice ConstraintGuard where top  = ConstraintGuard IS.empty
instance              FL.DecTop ConstraintGuard where isTop = IS.null . getConstraintGuard

instance PrettyM t ConstraintGuard where prettyM (ConstraintGuard guard) = PP.pretty <$> (map PP.pretty <$> IS.toList guard )

watch :: Constraints h t -> ConstraintGuard
watch = ConstraintGuard . IS.fromList . toList . allConstrIds 

watching :: forall h t r. UF_ h t r (Constraints h t) -> (ConstraintGuard -> UF_ h t r (Constraints h t)) -> UF_ h t r (Constraints h t)
watching m f = m >>= \cs -> (cs /\) <$> f (watch cs)

mkConstraintGuard :: [ConstraintId] -> ConstraintGuard
mkConstraintGuard = ConstraintGuard . IS.fromList

----------------------------------------------
-- Blockers                                 --
    ----------------------------------------------

data BlockerBase = ConstraintAll  ConstraintGuard
                 | MetaGuard      Guard

class BlockersOn a where blockersOn :: a -> Blockers
instance BlockersOn Guard where blockersOn = FL.inj . MetaGuard
instance BlockersOn ConstraintGuard where blockersOn = FL.inj . ConstraintAll 
instance BlockersOn GuardLattice where blockersOn = FL.evaluate . fmap anyMeta

anyMeta :: Guard -> Blockers
anyMeta = blockersOn

allConstraints :: ConstraintGuard -> Blockers
allConstraints = blockersOn

-- Rules for simplifying sets of base elements
instance FL.FreeLatticeBase BlockerBase where
  simpleJoin as =
    let (metas, rest) =
         let go [] = ([],[])
             go (MetaGuard e:zs) = let ~(xs,ys) = go zs in (e:xs,  ys)
             go (          r:zs) = let ~(xs,ys) = go zs in (  xs,r:ys)
         in
         go as
      
        metas' = joins metas
    in
    joins . map FL.inj .
      (if bottom == metas' then id else (MetaGuard metas':))
        $ rest


  simpleMeet as =
    let (constrs, rest) =
         let go [] = ([],[])
             go (ConstraintAll e:zs) = let ~(xs,ys) = go zs in (e:xs,  ys)
             go (              r:zs) = let ~(xs,ys) = go zs in (  xs,r:ys)
         in
         go as
      
        constrs' = meets constrs
    in
    meets . map FL.inj .
      (if top == constrs' then id else (ConstraintAll constrs':))
        $ rest

instance PrettyM t BlockerBase where                
  prettyM (MetaGuard guard)     = prettyM guard
  prettyM (ConstraintAll guard) = prettyM guard

type Blockers = FreeLattice BlockerBase 

data Blocked a = TryAgainWhen Blockers 
               | NotBlocked   a

metaLattice :: GuardLattice -> Blockers
metaLattice = FL.evaluate . fmap anyMeta

-- Convenience functions for WHNF and Blockers
-------------------------------------------------
whnfViewOrBlockers :: MonadTerm t m => Term t -> m (Either (Blockers, Term t) (Term t, TermView t))
whnfViewOrBlockers = wfViewOrBlockers whnf

wfViewOrBlockers :: (MonadTerm t m, BlockedTerm t a) => (t -> m a) -> Term t -> m (Either (Blockers, Term t) (Term t, TermView t))
wfViewOrBlockers f = f >=> wfBlockers >=> \case
    (Top,t') -> Right . (t',) <$> view t'
    s        -> pure$ Left s

whnfBlockers :: MonadTerm t m => Term t -> m (Blockers, Term t)
whnfBlockers = wfBlockers <=< whnf

whnfMetaBlockers :: MonadTerm t m => Term t -> m (Blockers, Term t)
whnfMetaBlockers = wfBlockers <=< whnfMeta

wfBlockers :: (BlockedTerm t a, MonadTerm t m) => a -> m (Blockers, Term t)
wfBlockers t' = do 
  case isBlocked t' of
    Nothing -> (Top,) <$> ignoreBlocking t'
    Just bs -> (anyMeta bs,) <$> ignoreBlocking t'


-- Toolkit for writing blocking functions in a monad
-------------------------------------------------------

class BlockerWrapper bs where
  fromBlockers :: Blockers -> bs
  toBlockers   :: bs -> Blockers
instance BlockerWrapper Blockers where
  fromBlockers = id
  toBlockers   = id
type BlockerMonoid bs = (BlockerWrapper bs, Monoid bs)
deriving instance BlockerWrapper (Meet Blockers)
deriving instance BlockerWrapper (Join Blockers)

type BlockerT_ m a = forall bs. BlockerMonoid bs => WriterT bs m a
type BlockerT m a = forall bs. BlockerWrapper bs => WriterT bs m a
censorWriterT :: (Functor m) => (a -> b) -> WriterT a m c -> WriterT b m c
censorWriterT f = mapWriterT (fmap $ second f)

-- | Use `and` as the joiner
blockAnd :: (Functor m) => WriterT (Meet Blockers) m a -> BlockerT m a
blockAnd = censorWriterT $ fromBlockers . getMeet

-- | Use `and` as the joiner
blockOr :: (Functor m) => WriterT (Join Blockers) m a -> BlockerT m a
blockOr = censorWriterT $ fromBlockers . getJoin 

runBlockerT :: BlockerT m a -> m (a, Blockers)
runBlockerT = runWriterT 

blockOn :: Applicative m => Blockers -> BlockerT m ()
blockOn bs = WriterT $ pure ((), fromBlockers bs) 

onBlocked :: (BlockedTerm t a, Monad m) => a -> BlockerT_ m ()
onBlocked a = mapM_ blockOn $ fmap anyMeta $ isBlocked a

{-# INLINE getBlocker #-}
getBlocker :: BlockerT Identity () -> Blockers 
getBlocker m = snd $ runIdentity $ runBlockerT m

{-# INLINE blockWfView #-}
blockWfView :: (BlockedTerm t a, MonadTerm t m) => a -> BlockerT_ m (TermView t)
blockWfView a = do
  onBlocked a
  lift$ ignoreBlocking_ a

-- Blocking for boolean results

{-# INLINE blockUnless #-}
blockUnless :: (Monad m) => Bool -> BlockerT m Bool
blockUnless b = WriterT $ pure (b, fromBlockers $ fromBool b)

{-# INLINE finalWhen #-}
finalWhen :: (Functor m, Monoid bs) => (a -> Bool) -> WriterT bs m a -> WriterT bs m a
finalWhen final = mapWriterT $ fmap (\(a,bs) -> if final a then (a,mempty) else (a,bs))

-- | Check if a type is the unit type                 --
--                                                    --

--    and  records whose fields are all unit types.   --
--------------------------------------------------------
isUnitRecord :: MonadTerm t m => t -> m Blockers
isUnitRecord = go
  where
    go ty = whnfViewOrBlockers ty >>= \case
      Left  (bs, _) -> return bs
      Right (_ , App (Def (OTyCon tyCon)) _) ->
                  getDefinition tyCon >>= \case
                    Constant _ (Record _ []) -> return Top
                    _ -> return FL.Bottom
      Right (_ , _) -> return FL.Bottom
    

-- Constraints
----------------------

data C h t = C { constrLoc  :: SrcLoc
               , constrId   :: ConstraintId
               , blockers   :: Blockers
               , constraint :: Constraint h t
               }

instance Unifier h t => PrettyM t (C h t) where
  prettyM C{constrLoc,constrId,blockers,constraint} = do
        cDoc <- prettyM constraint
        mvsDoc <- prettyM blockers
        return$ PP.line <> "** Problem #" <+> PP.pretty constrId <+> PP.pretty constrLoc <+>
                    "[" <> mvsDoc <> "]" $$ cDoc

type Constraints h t = Alg (C h t)

-- | prop> simplify x == Top  <==>  allConstrIds x == []
allConstrIds :: Constraints h t -> Seq ConstraintId
allConstrIds = Seq.fromList . fmap constrId . toList 

type History h t = History' (Elaborate.Constraint t) (Constraint h t)

data SolveState h t = SolveState
  { _ssConstraintCount :: !ConstraintId
  , _ssConstraints     :: !(Constraints h t)
  , _ssHistory         :: Seq (History h t)
  , _ssIsSolved        :: Refinement ConstraintId
  , _ssNotifiedMetas   :: Maybe Meta
  }

class UnifierImpl h where
  unifierShortName, unifierLongName :: String
  unifierDict :: Unify t => Dict (Unifier h t)
  default unifierDict :: Unifier h t => Dict (Unifier h t)
  unifierDict = Dict

class (IsTerm t
      ,PrettyM t (Constraint h t)
      ,ExpandGuards (Constraint h t)
      ,UnifierImpl h
      ) => Unifier (h :: K.*) t where

  data Constraint h t

  -- | Translates a constraint into the internal representation
  makeConstraint :: Ctx t -> (Term t :∈ Type t)
                          -> (Term t :∈ Type t)
                          -> UF h t (Constraints h t)

  -- | Refines an unblocked constraint
  refine         :: Constraint h t -> UF h t (Constraints h t)

  -- | This method will be called once and only once per metavariable
  --   in the signature.
  newMeta :: Meta -> UF h t (Constraints h t)
  newMeta _ = return Top

class ExpandGuards a where
  expandGuards :: a -> Refinement ConstraintId -> a

instance Unifier h t => ExpandGuards (C h t) where
  expandGuards c@C{blockers,constraint} r = c{blockers   = expandGuards blockers r
                                             ,constraint = expandGuards constraint r
                                             }

instance ExpandGuards Blockers where expandGuards = traverse expandGuards
instance ExpandGuards BlockerBase where
  expandGuards mg@MetaGuard{} = pure mg
  expandGuards (ConstraintAll cg) = ConstraintAll <$> expandGuards cg
instance ExpandGuards ConstraintGuard where expandGuards (ConstraintGuard cs) = ConstraintGuard <$> R.unsolvedChildrenN cs

type UF h t a = forall r. UF_ h t r a
type UF_ h t r = TC t r (SolveState h t)

makeLenses ''SolveState

notifyNewMetas :: forall h t. Unifier h t => UF h t (Constraints h t)
notifyNewMetas = do
  lastNotifiedMv  <- use ssNotifiedMetas
  maxMv           <- sigDefinedMetaMaxBound <$> askSignature

  (Meet cs, newLast) <-
    -- We accumulate all the constraints, and keep track of the last metavariable
    -- which we notified about.
    --
    -- Note that all new metas will have a larger identifier.
    execWriterT @_ @(Meet (Constraints h t), Last Meta) $
      forM_ @[] [maybe 0 ((+1) . IS.repr) lastNotifiedMv..maxMv] $ \i -> do
        (lift$ runMaybeT (IS.full i)) >>= \case
          Just mv -> do
            csMv <- lift$ elaborateNewMeta mv 
            tell (Meet csMv, Last$ Just mv)
          Nothing -> return ()

  -- Update the last notified meta (if it has been notified)
  forM_ @Maybe (getLast newLast) $ \newLast' -> do
    ssNotifiedMetas .= Just newLast'

  return cs
  where
    -- Show debugging information, and set source location for the constraints
    -- generated by the notification.
    elaborateNewMeta ::  forall h t. Unifier h t => Meta -> UF h t (Constraints h t)
    elaborateNewMeta mv =
      let loc = srcLoc mv in
      let msg = do
            constrsDoc <- runNamesT C0$ prettyM mv
            return $
              "location:" //> PP.pretty loc $$
              "new meta:" //> constrsDoc
      in
      debugBracket DL.Meta_constraint msg $ 
        atSrcLoc loc $ withParent (ParentMeta mv) $ do
          cs <- newMeta mv
          whenDebug$ debug "elaborated to:" $ runNamesT C0$ prettyM cs
          return cs


initSolveState :: forall h t. SolveState h t
initSolveState = SolveState 0 top [] R.empty Nothing

getUnsolvedProblems :: UF h t (Constraints h t)
getUnsolvedProblems = use ssConstraints

-- | Creates a new (blocked) constraint
--   It is important that creating a constraint does not alter the state of the unifier.
newBlockedConstraint :: Unifier h t => Blockers -> Constraint h t -> UF h t (Constraints h t)
newBlockedConstraint blockers constraint = do 
  constrLoc <- askSrcLoc
  constrId <- ssConstraintCount <%= (+1)
  -- Debugging

  debugWhenLabel DL.NewConstraint $ runNamesT C0$ do
    constrDoc <- prettyM constraint
    mvsDoc <- prettyM blockers
    return $
      "constrId:" //> PP.pretty constrId $$
      "mvs:" //> mvsDoc $$
      "constr:" //> constrDoc

  return$ Base C{constrId,constrLoc,blockers=FL.simplify blockers,constraint}

-- | Creates a new unblocked constraint.
--   WARNING: If a constraint is refined to an unblocked constraint without making
--   any sort of "progress", this could lead to an infinite loop in the unifier. 
newConstraint :: Unifier h t => Constraint h t -> UF h t (Constraints h t)
newConstraint = newBlockedConstraint top

sequenceConstraints :: Unifier h t => Constraints h t -> Constraint h t -> UF h t (Constraints h t)
sequenceConstraints Top c2  = refine c2
sequenceConstraints scs1 c2 = (scs1 >>:) <$> newConstraint c2

done :: UF h t (Constraints h t)
done = pure top

cannotSolve :: PP.Doc -> UF h t α
cannotSolve doc = typeError PP.Error{errCode=1,errDoc=doc}

data Parent h t =
    Elaborator (Elaborate.Constraint t)
  | ParentMeta Meta
  | Constraint{ constrId   :: ConstraintId
              , constraint :: Constraint h t
              }

withParent :: Unifier h t => Parent h t -> UF h t (Constraints h t) -> UF h t (Constraints h t)
withParent (ParentMeta parentMv) m = do
  stats <- confStats <$> readConf
  if stats then do
      (cs,time) <- timingRaw m
      ssHistory %= (|> History.HistoryMeta{metaId = IS.repr parentMv, metaLoc=srcLoc parentMv, children=allConstrIds cs,time})
      return cs
  else
      m
  
withParent (Elaborator e) m = do
  -- Store elaborated constraint information either for auditing or for statistics
  stats <- confStats <$> readConf
  audit <- confUnifyAudit <$> readConf
  if stats || audit then do
    (cs,time) <- if stats then timingRaw m else (,0) <$> m
    eDoc      <- if stats then prettyM_ e else pure mempty
    ssHistory %= (|> History.Elaborator{constrLoc=srcLoc e, constraint=eDoc, elabConstraint=e, children=allConstrIds cs,time})
    return cs
  else
    m

withParent Constraint{constrId,constraint} m = do
  cs <- (confStats <$> readConf) >>= \case
    False -> m
    True  -> do
      (cs,time) <- timingRaw m
      loc <- askSrcLoc
      cDoc <- runNamesT C0$ prettyM constraint
      ssHistory %= (|> History.Refined{constrId,constrLoc=loc, constraint=cDoc, termConstraint=constraint, children=allConstrIds cs,time})
      return cs

  -- Keep track of whether the constraint is solved, or still has
  -- children left.
  let children = toList$ allConstrIds cs 
  ssIsSolved %= R.branch constrId children
  -- Whenever a constraint is solved, show the current status in the debug output
  when (null children) $ debug "solved: " $
    mconcat <$> sequence [ PP.pretty . R.countSolved <$> use ssIsSolved
                         , pure "/"
                         , PP.pretty . R.countAll    <$> use ssIsSolved
                         ]
  return cs

renderHistory :: (Unifier h t, MonadTerm t m) => SolveState h t -> m [History.Rendered] 
renderHistory state@SolveState{_ssIsSolved} = do
  let history = state ^. ssHistory
  leftovers <- (execWriterT . flip runReaderT [] . go) $ state ^. ssConstraints
  History.render (leftovers <> history)
  where
    go :: Alg _ -> ReaderT _ (WriterT _ _) (Seq _)
    go Top = pure []

    go (Conj cs)  = join <$> mapM go cs

    go (a :>>: b) = do
      cids   <- go a 
      cids'  <- local (\_ -> cids) $ go b
      return cids' 

    go (Base c) = do
      let C{constrLoc,constrId,blockers,constraint} = expandGuards c _ssIsSolved
      waitingFor <- ask
      blockedBy <- runNamesT C0$ prettyM blockers
      constraintDoc <- runNamesT C0$ prettyM constraint
      tell [History.Blocked{constrLoc,constrId,waitingFor,blockedBy,constraint=constraintDoc,termConstraint=constraint}]
      return [constrId]

{-
auditHistory :: (MonadTerm t m, IsTerm t) => SolveState h t -> m (Either PP.Doc Nat)
auditHistory = audit' >=> \case
  Right n  -> return$ Right n
  Left err -> Left <$> prettyM_ err
                 -}

-- | Note how the audit does not depend on the unifier implementation
auditState :: (MonadTerm t m, IsTerm t) => SolveState h t -> m (Either (SrcLoc, CheckError t) Nat)
auditState state = do
   let history = state ^. ssHistory
   let solved  = state ^. ssIsSolved
   let es = [(elabConstraint, constraint, children) | History.Elaborator{elabConstraint,constraint,children} <- toList history]
   let total = length es
   runExceptT$ foldM (\(!acc) -> \case
      (i :: Nat,(ec@(Elaborate.JmEq _ ctx (tyA :∋ tA) (tB :∈ tyB)),prevDoc,children)) -> do
        let msg = do
              ecDoc <- prettyM_ ec
              return$ "original:" //> prevDoc $$
                      "normalized:" //> ecDoc 
        debugBracket DL.Audit msg $ do
          debug "" (pure$ PP.pretty i <> "/" <> PP.pretty total)
          let cs = toList children
          if all (`R.isSolved` solved) cs then do
            debug "check type" (pure "")
            lift (genericNfEq ctx ((tyA,tyB) :∈ set)) >>= \case
              Right () -> return ()
              Left (msg,ctx',t)  -> throwE (srcLoc ec, FailedAudit cs (PP.pretty msg) ctx' t)
            debug "check term" (pure "")
            lift (genericNfEq ctx ((tA,  tB) :∈ tyA)) >>= \case
              Right () -> return ()
              Left (msg,ctx',t)  -> throwE (srcLoc ec, FailedAudit cs (PP.pretty msg) ctx' t)
            return $! acc + 1
          else
            return $! acc)
              0 (zip [1..] es)

audit :: IsTerm t => UF h t Nat 
audit = use id >>= auditState >>= \case
  Right i  -> return i
  Left (loc,err) -> atSrcLoc loc$ checkError err
 
-- More about guards

isSolved :: ConstraintGuard -> UF h t Bool
isSolved g = R.areAllSolved (getConstraintGuard g) <$> use ssIsSolved

shouldAttempt :: IsTerm t => Blockers -> UF h t Bool 
shouldAttempt = fmap FL.evaluate . traverse (\case
                               MetaGuard guard    -> guardIsInstantiated guard
                               ConstraintAll cids -> isSolved cids)

solve :: forall h t. Unifier h t => Elaborate.Constraints t -> UF h t ()
solve es = debugBracket DL.AdLibitum (pure "") $ do
  -- 0. Elaborate the new constraints
  csElab  <- meets <$> mapM elaborateConstraint es
  -- 1. Obtain the currently unsolved constraints
  use ssConstraints
  -- 2. Add the new constraints from elaboration, before the old constraints
    <&> (csElab /\)
  -- 3. While progress is made (i.e. the `refine` method is called on a constraint) … 
      >>= adLibitum (\csCurr -> do
                -- 3.1. Notify of any new metas which have been added since last time
                csMvs <- notifyNewMetas
                -- 3.2. Refine unblocked constraints 
                runWriterT @Any $ go (csCurr /\ csMvs))
  -- 4. Store the final list of new, blocked constraints.
      >>= (ssConstraints .=)
  
  where
    elaborateConstraint e@(Elaborate.JmEq loc ctx (type1 :∋ t1) (type2 :∋ t2)) =
      let msg = do
            constrsDoc <- runNamesT C0$ prettyM e
            return $
              "location:" //> PP.pretty loc      $$
              "constraint:" //> constrsDoc
      in
      debugBracket DL.Elaborate_constraint msg $ 
        atSrcLoc loc $ withParent (Elaborator e) $ do
          cs <- makeConstraint ctx (t1 :∈ type1) (t2 :∈ type2)
          whenDebug$ debug "elaborated to:" $ runNamesT C0$ prettyM cs
          return cs

    -- | Runs the action while it says 'yes' (i.e. while the second component equals `Any True`
    adLibitum :: forall a m. Monad m => (a -> m (a, Any)) -> a -> m a
    adLibitum f a = do
      (a', Any more) <- f a
      if more then adLibitum f a' else return a'

    go :: forall r. Constraints h t -> WriterT Any (UF_ h t r) (Constraints h t) 
    go c@(Base C{constrLoc,constrId,blockers,constraint}) = do
        b <- lift$ shouldAttempt blockers
        case b of
          True  -> do
            tell (Any True)
            let msg = runNamesT C0$ do
                  constrDoc <- prettyM constraint
                  return $
                    "constrId:" //> PP.pretty constrId $$
                    "constr:" //> constrDoc
            debugBracket DL.Solve msg $
              -- This does not seem to affect performance that much,
              -- but it does help reduce the number of jumps when doing debug
              -- traces.
              go =<< (lift$ atSrcLoc constrLoc $ withParent (Constraint constrId constraint) $ do
                  cs <- refine constraint
                  whenDebug $ debug "refined to:" $ runNamesT C0$ prettyM cs
                  return cs)

          False -> return c 

    go (a :>>: b) =
      go a >>= \case
        Top -> go b
        a'  -> return$ a' >>: b

    go (Conj as) = meets <$> traverse go (toList as)


-- instance Unifier h t => PrettyM t (SolveState h t) where
printSolveState :: forall m h t. (Unifier h t, MonadTerm t m) => SolveState h t -> m ()
printSolveState state@(SolveState{
                   _ssConstraints=unConj -> cs
                  ,_ssIsSolved}
                 ) = do
     detailed <- confProblemsReport <$> readConf
     stats <- confStats <$> readConf
     tell $ "-- Total problems:" <+> PP.pretty (R.countAll _ssIsSolved) <> PP.line
     tell $ "-- Unsolved problems:" <+> PP.pretty (length cs)
     when detailed $ forM_ cs $ \c -> do
       tell $ PP.line <> "------------------------------------------------------------------------" <> PP.line
       tell =<< prettyM_ (traverse expandGuards c _ssIsSolved)
     when stats $ do
       tell PP.line
       f <- liftIO . History.writeHistory =<< renderHistory state
       tell$ "-- Unification history: " <+> PP.pretty f
     where
       tell :: PP.Doc -> m ()
       tell = liftIO . putStrLn . PP.render
     

