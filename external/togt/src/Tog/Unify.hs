{-# LANGUAGE AllowAmbiguousTypes #-} 
{-# LANGUAGE OverloadedLists #-} 
-- | Solves unification problems.
module Tog.Unify
  ( SolveState(..)
  , initSolveState
  , solve
  , solveAll
  , solvers
  , Unify
  , printSolveState
  ) where

import           Data.List (find)

import           Tog.Prelude
import           Tog.Instrumentation
import           Tog.Term
import           Tog.Monad
import           Tog.Elaborate.Constraint
import           Tog.Unify.Common (Unify)
--import qualified Tog.Unify.Heterogeneous          as Heterogeneous

-- Modular implementation
import qualified Tog.Unify.Class                   as Class

import           Tog.Unify.Impl

data Solver' = Solver' { unpack :: forall t. Unify t => SolveState t }

data SolveState t = forall h. (Class.Unifier h t) => SolveState
  { sState    :: Class.SolveState h t
  , sSolve    :: forall r. (Unify t) => Constraints t -> TC t r (Class.SolveState h t) ()
  }

type Solver = CmdModule Solver'

pattern Solver :: String
                    -> String
                    -> (forall t. Unify t => SolveState t)
                    -> CmdModule Solver'

pattern Solver a b c = CmdModule a b (Solver' c)


coreSolveState :: forall h t. Class.Unifier h t => SolveState t
coreSolveState = SolveState{
                   sState = Class.initSolveState
                 , sSolve = Class.solve @h
                 } 

mkSolver :: forall h. Class.UnifierImpl h => Solver
mkSolver = Solver (Class.unifierShortName @h) (Class.unifierLongName @h) go
  where
    go :: forall t. Unify t => SolveState t
    go = case Class.unifierDict @h @t of
      Dict -> coreSolveState @h

solvers :: [Solver]
solvers = [mkSolver @Simple, mkSolver @Twin, mkSolver @Mock]

initSolveState :: (Unify t, MonadConf m) => m (SolveState t)
initSolveState = do
  solver <- confSolver <$> readConf
  case find ((== solver) . opt) solvers of
    Just (cmd -> prog) -> return$ unpack prog
    Nothing -> error $ "Unsupported solver " ++ solver

solve :: (Unify t) => Constraint t -> TC t r (SolveState t) ()
solve = solveAll . (\x -> [x])

solveAll :: (Unify t) => Constraints t -> TC t r (SolveState t) ()
solveAll c = do
  SolveState ss solve' <- get
  ss' <- magnifyStateTC (const ss) $ solve' c >> get
  put $ SolveState ss' solve'

--instance PrettyM t (SolveState t) where
printSolveState :: forall m h t. (MonadTerm t m) => SolveState t -> m ()
printSolveState (SolveState ss _) = Class.printSolveState ss
-- instance Unifier h t => PrettyM t (SolveState h t) where
