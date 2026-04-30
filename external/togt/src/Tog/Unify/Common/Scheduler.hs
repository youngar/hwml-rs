{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Tog.Unify.Common.Scheduler (
  Blockers(..),
  ConstraintIds,
  Solver,
  defer,
  CExecResult(..),
  ConstraintId) where

import           Tog.Prelude

import Algebra.Lattice

import qualified Data.Set as S
import           Data.Set (Set)

import qualified Data.HashMap.Strict as HM
import           Data.HashMap.Strict (HashMap)

import           Tog.Names
import           Tog.Term
import           Tog.Instrumentation.Debug
import qualified Tog.Instrumentation.Debug.Label as DL
import           Tog.Instrumentation.Conf
import           Tog.Unify.Common.Graph
import           Tog.Monad
import           Tog.Error

import           Tog.PrettyPrint                  (($$), (<+>), (//>))
import qualified Tog.PrettyPrint                  as PP

import qualified Tog.Elaborate                    as Elaborate

import           Control.Lens
import           Control.Monad.State.Strict
import           Control.Monad.Loops
import           Control.Monad.Writer.Strict (tell, execWriterT)

import           Data.Monoid ((<>))

-- Defining blocker sets 
----------------------------------------------------
data Blockers = AnyOf !(Set Blockers)
              | AllOf !(Set Blockers)
                -- ^ This does not block if the list is empty
              | AnyMeta Guard
              | AllConstraint !ConstraintIds
              deriving (Eq, Ord)

instance PrettyM t Blockers where
  prettyM (AnyOf mvs) = prettyM (S.toList mvs) <&> \doc -> "any(" <+> doc <+> ")"
  prettyM (AllOf mvs) = prettyM (S.toList mvs) <&> \doc -> "all(" <+> doc <+> ")"
  prettyM (AnyMeta mvs) = prettyM mvs <&> \doc -> "any(" <+> doc <+> ")"
  prettyM (AllConstraint cs) = return$ "all(" <+> PP.pretty cs <+> ")"

instance JoinSemiLattice Blockers where
  AnyOf bs1      \/ AnyOf bs2       = AnyOf$ bs1 <> bs2
  AnyOf bs1      \/ bs2           = AnyOf$ S.insert bs2 bs1
  bs1          \/ AnyOf bs2       = AnyOf$ S.insert bs1 bs2
  AnyMeta mvs1 \/ AnyMeta mvs2  = AnyMeta$ mvs1 <> mvs2
  bs1          \/ bs2           = AnyOf$ S.fromList [bs1, bs2]

instance BoundedJoinSemiLattice Blockers where
  bottom = AnyOf mempty

instance MeetSemiLattice Blockers where
   AllOf bs1     /\ AllOf bs2       = AllOf$ bs1 <> bs2
   AllOf bs1     /\ bs2           = AllOf$ S.insert bs2 bs1
   bs1         /\ AllOf bs2       = AllOf$ S.insert bs1 bs2
   AllConstraint a /\ AllConstraint b = AllConstraint$ a <> b
   bs1         /\ bs2           = AllOf$ S.fromList [bs1, bs2] 

instance BoundedMeetSemiLattice Blockers where
  top = AllOf mempty 

shouldAttempt :: Solver c => Blockers -> TCS r c Bool
shouldAttempt (AnyOf mvs) = anyM shouldAttempt $ S.toList mvs
shouldAttempt (AllOf mvs) = allM shouldAttempt $ S.toList mvs
shouldAttempt (AnyMeta mvs) = guardIsInstantiated mvs
shouldAttempt (AllConstraint cs) = allM constraintIsSolved (S.toList cs)

-- | If this overflows, all hell will break loose.
--   On the other hand, the interning library uses `Int` also for the identifiers,
--   and there are clearly many more distinct terms than constraints. 
type ConstraintId = Int

type Constraints c = [(ConstraintId, Blockers, c)]
type Constraints_ c = [(Blockers, c)]

-- | The phantom parameter does nothing, but we might make it use it in the future
type ConstraintIds = Set ConstraintId

data SolveState c = SolveState
  {
  -- | Sequential identifiers for constraints (in case they are needed).
  --   The user may choose to generate their own.
    _ssConstraintCount :: !ConstraintId
  -- | Constraint tree
  --   We keep track on what is required in order to solve a constraint.
  --   It can either be a 'c' proper (perhaps waiting for some
  --   blockers to be instantiated), or just a list of constraints it has
  --   been elaborated to.                          
  , _ssConstraints     :: !(Forest Blockers c) 
  -- | Location of the last added constraint. Useful for tracking progress
  , _ssLoc             :: !SrcLoc
  -- | Hash table of seen constraints
  , _ssSeenConstraints :: !(HashMap c ConstraintId)
  }

type TCS r c = TC (CTerm c) r (SolveState c)

-- Lenses
-----------
ssConstraints :: Lens' (SolveState c) (Forest Blockers c) 
ssConstraints f x = (\_ssConstraints ->  x{_ssConstraints}) <$> f (_ssConstraints x)

ssConstraintCount :: Lens' (SolveState c) ConstraintId
ssConstraintCount f x = (\_ssConstraintCount ->  x{_ssConstraintCount}) <$> f (_ssConstraintCount x)

ssLoc :: Lens' (SolveState c) SrcLoc
ssLoc f x = (\_ssLoc ->  x{_ssLoc}) <$> f (_ssLoc x)

ssSeenConstraints :: Lens' (SolveState c) (HashMap c ConstraintId)
ssSeenConstraints f x = (\_ssSeenConstraints ->  x{_ssSeenConstraints}) <$> f (_ssSeenConstraints x)

initSolveState :: SolveState c
initSolveState = SolveState 0 emptyForest noSrcLoc HM.empty

data CExecResult c = ReducesTo ConstraintIds
                   | WaitFor   Blockers c

class (IsTerm (CTerm c), PrettyM (CTerm c) c, HasSrcLoc c) => Solver c where
  type CTerm c

  -- | Solves a constraint in the scheduling monad
  execConstraint :: c -> TCS r c (CExecResult c)

  -- | Elaborate an heterogeneous constraint into the internal format 
  constraint :: Elaborate.Constraint (CTerm c) -> TCS r c c

  -- | Identify a constraint by a unique identifier. It is OK if
  --   the same constraint maps to two different identifiers, but not
  --   if different constraints map to the same identifier.              
  identifyConstraint :: c -> TCS r c ConstraintId         


-- | Continue solving this constraint, once the blockers are discharged 
--   
--   The constraint that is passed to `blockOn` must be “smaller” than the
--   one that we are trying to solve, once the blockers are discharged.
blockOn :: Solver c => Blockers -> c -> TCS r c (CExecResult c)
blockOn = (fmap.fmap) return WaitFor

-- | Deem this constraint solved once the following constraint id's are solved
reducesTo ::  Solver c => ConstraintIds -> TCS r c (CExecResult c)
reducesTo = fmap return ReducesTo
  
-- | A deferred constraint must be smaller than the constraint that is
--   being elaborated.
defer :: Solver c => Blockers -> c -> TCS r c (ConstraintIds)
defer mvs constr = do
  constrId <- identifyConstraint constr
  let msg = do
        mvsDoc <- prettyM_ mvs
        constrDoc <- prettyM_ constr
        return $
          "constrId:" //> PP.pretty constrId $$
          "mvs:" //> mvsDoc $$
          "constr:" //> constrDoc
  debugBracket DL.NewConstraint msg $
    newConstraint mvs constrId constr


-------------------
-- Internal
-------------------
constraintIsSolved :: (Solver c) => ConstraintId -> TCS r c Bool
constraintIsSolved constrId = zoomTC ssConstraints$ hasWithered constrId

-- | Attempts to solve a constraint, unless it has already been reduced to
--   further constraints.
newConstraint :: (Solver c) => Blockers -> ConstraintId -> c -> TCS r c (ConstraintIds)
newConstraint mvs constrId constr =
  zoomTC ssConstraints (getStatus constrId) >>= \case
    Nothing -> attempt mvs constrId constr
    Just (_, Withered) -> do
      debug_ "constraint solved" ""
      return []
    Just (_, Fresh cs) -> do
      debug_ ("constraint attempted. waiting on " <> PP.pretty cs) ""
      return [constrId]
    Just (_, Leaf mvs') -> do
      mvsDoc <- prettyM_ mvs
      mvsDoc' <- prettyM_ mvs'
      debug_ ("constraint blocked on " <> mvsDoc' <> "." $$
              "formerly blocked on " <> mvsDoc <> ".") ""
      attempt (mvs \/ mvs') constrId constr
  where
    -- Attempt must not be called if `constrId` has branched already
    attempt :: Solver c => Blockers -> ConstraintId -> c -> TCS r c (ConstraintIds)
    attempt mvs constrId constr =
      do
        zoomTC ssConstraints $ upsertLeaf constrId mvs constr
        shouldAttempt mvs >>= flip when solvePending
        S.fromList <$> filterM constraintIsSolved [constrId]
      
-- | Attempts to solve a constraint if it is unblocked
--   Otherwise, it will add it to the tree forest, or update it in
--   place.

-- | Conjunction of constraints
conj :: Solver c => [c] -> TCS r c ConstraintIds 
conj [] = return []
conj (c:cs) = (<>) <$> defer top c <*> conj cs

sequenceConstraints :: Solver c => ConstraintIds -> c -> TCS r c ConstraintIds
sequenceConstraints cs c = defer (AllConstraint cs) c

-- | This function generates unique constraint identifiers
genericIdentify :: c -> TC (CTerm c) r (SolveState c) ConstraintId         
genericIdentify _ = do
  ssConstraintCount %= (+1)
  use ssConstraintCount

-- | This function generates unique identifiers, but reuses the same identifier
--   for the same constraint.
hashIdentify :: (Eq c, Hashable c) => c -> TC (CTerm c) r (SolveState c) ConstraintId         
hashIdentify c = do
  (HM.lookup c <$> use ssSeenConstraints) >>= \case
    Nothing -> do
      cId <- genericIdentify c
      ssSeenConstraints %= HM.insert c cId
      return cId
    Just cId -> return cId
          

newtype UnzoomSSConstraints c m a = UnzoomSSConstraints { zoomSSConstraints :: m a }
                                deriving (Functor,Applicative,Monad)
                                                                                                               
instance MonadState (SolveState c) m => MonadState (Forest Blockers c) (UnzoomSSConstraints c m) where
  get = UnzoomSSConstraints$ use ssConstraints 
  put = UnzoomSSConstraints . assign ssConstraints
  --state = UnzoomSSConstraints . fmap state
  
-----------

solve :: Solver c => Elaborate.Constraint (CTerm c) -> TCS r c ()
solve c' = do
  debugBracket_ DL.Solve "" $ do
    ssLoc .= srcLoc c'
    c <- constraint c'
    void$ defer top c

solvePending :: forall c r. Solver c => TCS r c () 
solvePending = do
    debugWhenLabel DL.Status $ do
      unsolvedCount <- zoomTC ssConstraints$ getNumberOfLeaves 
      locDoc <- use ssLoc
      return$ PP.pretty locDoc //> "Unsolved problems:" //> PP.pretty unsolvedCount
    go
  where
    go = do
      progress <- zoomSSConstraints @c $ runExceptT$ withLeaves @c $ \constrId mvs constr -> lift$ UnzoomSSConstraints$
        shouldAttempt mvs >>= \case
          False -> return$ LeafNoOp
          True  ->
            solveConstraint constrId constr >>= \case
              WaitFor mvs constr' -> do
                constrId' <- identifyConstraint constr
                if constrId == constrId' then
                  return$ LeafRelabel mvs 
                else
                  LeafBranch <$> defer mvs constr'
              ReducesTo cs -> return$ LeafBranch cs
      case progress of
        Left cycle -> typeError$ ppGenericError$ "Cycle in reduction rules:" <+> PP.pretty cycle <+> "."
        Right progress | progress > 0 -> go -- Another ride
                       | otherwise    -> return ()

solveConstraint :: Solver c => ConstraintId -> c -> TCS r c (CExecResult c)
solveConstraint constrId constr0 = do
  let msg = do
        constrDoc <- prettyM_ constr0
        return $
          "constrId:" //> PP.pretty constrId $$
          "constr:" //> constrDoc
  debug "solveConstraint" msg
  execConstraint constr0


instance PrettyM t c => PrettyM t (SolveState c) where
  prettyM (SolveState _ cs0 _ _) = do
     detailed <- confProblemsReport <$> readConf
     let go = do
           unsolved <- getUnsolvedNodes
           leaves   <- getLeaves
           tell $ "-- Unsolved constraints:" <+> PP.pretty (length leaves)
           when detailed $ do
             forM_ unsolved $ \(cId, c, cIds) -> do
                   tell $ PP.line <> "------------------------------------------------------------------------"
                   cDoc <- lift$ prettyM_ c
                   tell $ PP.line <> "** " <+> PP.pretty cId <+> ", " <+> " reduced to "
                             <+> PP.pretty cIds $$ cDoc

             forM_ leaves $ \(cId, mvs, c) -> do
                   tell $ PP.line <> "------------------------------------------------------------------------"
                   cDoc <- lift$ prettyM_ c
                   mvsDoc <- lift$ prettyM_ mvs
                   tell $ PP.line <> "** Waiting on" <+> PP.pretty cId <+>
                          "[" <> mvsDoc <> "]" $$ cDoc

     flip evalStateT cs0$ execWriterT$ go
