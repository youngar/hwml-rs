module Tog.Unify.Common.Graph (
  Forest,
  NodeId,
  emptyForest,
  upsertLeaf,
  branchLeaf,
  getStatus,
  withLeaves,
  getLeaves,
  getNumberOfLeaves,
  getUnsolvedNodes,
  WithLeavesResult(..),
  Status(..),
  hasWithered) where

import           Control.Lens (Lens', (%=), use, (<&>)) 

import qualified Data.Map as M
import           Data.Map (Map)

import qualified Data.Set as S
import           Data.Set (Set)

import           Data.Default                 
import           Data.List (sortBy)
import           Data.List.NonEmpty (NonEmpty(..))

import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Writer.Strict

import           Prelude
import           Data.Monoid (Any(..))

-- Only thing here that depends on Tog
import           Tog.Instrumentation.Debug (fatalError)
#include "impossible.h"

-------------------------
-- Constraint graph
-------------------------
type NodeId = Int
type NodeIds = Set Int
type Natural = Int
                 
instance Default (Forest bs c) where
  def = Forest M.empty

-- | An acyclic graph

data Node c bs = NodeLeaf      c bs
               | NodeBranch    c [NodeId]

data Status bs = Leaf bs
               | Withered 
               | Fresh (NonEmpty NodeId)

data Forest bs c = Forest {
   -- | Main Graph
   --   It must have no cycles!
   _children  :: !(Map Int (Node c bs))
   
 }
-- Lenses
children :: Lens' (Forest bs c) (Map NodeId (Node c bs))
children f x = fmap (\_children -> x{_children}) (f (_children x))

emptyForest :: Forest bs c
emptyForest = Forest M.empty

lookupNode :: (MonadState (Forest bs c) m) => NodeId -> m (Maybe (Node c bs))
lookupNode nodeId = do
  (M.lookup nodeId <$> use children) >>= mapM (\case
    NodeBranch c cs -> do
      (cs', Any anyWithered) <- runWriterT$ filterM (hasWithered >=> ((>>) <$> tell . Any <*> (return . not))) cs
      when anyWithered $ children %= M.insert nodeId (NodeBranch c cs')
      return$ NodeBranch c cs'
    a -> return a)

hasWithered :: (MonadState (Forest bs c) m) => NodeId -> m Bool
hasWithered nodeId =
  getStatus nodeId <&> \case
    Just (_, Withered) -> True
    _ -> False
  
getStatus :: (MonadState (Forest bs c) m) => NodeId -> m (Maybe (c, Status bs))
getStatus nodeId = lookupNode nodeId <&> fmap (\case
  NodeLeaf c bs ->  (c, Leaf bs)
  NodeBranch c [] -> (c, Withered)
  NodeBranch c (n:ns) ->  (c, Fresh (n :| ns))
  )

-- | Add a new, blocked node to the tree.
--   O(n)
upsertLeaf :: (MonadState (Forest bs c) m) => NodeId -> bs -> c -> m ()
upsertLeaf nodeId bs constr =
  (M.lookup nodeId <$> use children) >>= \case
    Nothing            -> children %= M.insert nodeId (NodeLeaf constr bs) -- a new insertion
    Just (NodeLeaf{})   -> children %= M.insert nodeId (NodeLeaf constr bs) -- an update
    Just (NodeBranch{}) -> __IMPOSSIBLE__ -- An attempted node should not be added again

-- | Expand a node. A node must only be expanded once, and it must be a leaf (or
--   not be in the tree).
--   O(n²) (because of checking for cycles)
branchLeaf :: (MonadState (Forest bs c) m, MonadError [NodeId] m) => NodeId -> c -> Set NodeId -> m ()
branchLeaf nodeId constr (S.toList -> cs) =
  (M.lookup nodeId <$> use children) >>= \case
    Nothing            ->
      -- We allow for a node to be attempted without adding it first
      children %= M.insert nodeId (NodeBranch constr cs)
    Just (NodeLeaf{})   -> do
      -- Otherwise, change the blocked node into an attempted node
      -- 1. First, make sure that this does not introduce cycles
      maybeCycles <- nodeId `isDescendantOfAny` cs
      case maybeCycles of
        [] ->  -- 2. Then, if this will not introduce cycles, then update it.
               children %= M.insert nodeId (NodeBranch constr cs)
        cycle:_ ->
               -- 2. Otherwise, there is a cycle in the reduction rules. Throw an error.
               throwError cycle 
    Just (NodeBranch{}) -> __IMPOSSIBLE__  -- A node must not be branched more than once.

-- Here we should avoid recomputing the solved set for all nodes.
-- Instead, it should be dynamically updated, bottom-up.
getAllNodes :: (MonadState (Forest bs c) m) => m [(NodeId, c, Status bs)] 
getAllNodes = (M.keys <$> use children) >>= mapM (\nodeId -> getStatus nodeId <&> \(Just (c,status)) -> (nodeId,c,status))

getLeafIds :: (MonadState (Forest bs c) m) => m [NodeId]
getLeafIds = do
  all <- use children
  return$ revSort [ nodeId | (nodeId, NodeLeaf{}) <- M.toList all ]

getLeaves :: (MonadState (Forest bs c) m) => m [(NodeId, bs, c)]
getLeaves = do
  all <- use children
  return$ [ (nodeId, bs, c) | (nodeId, NodeLeaf c bs) <- M.toList all ]

getUnsolvedNodes :: (MonadState (Forest bs c) m) => m [(NodeId, c, NonEmpty NodeId)]
getUnsolvedNodes = do
  all <- getAllNodes 
  return [ (nodeId, c, cs) | (nodeId, c, Fresh cs) <- all ]

getNumberOfLeaves :: (MonadState (Forest bs c) m) => m Int
getNumberOfLeaves = length <$> getLeafIds

getNumberOfUnsolvedNodes :: (MonadState (Forest bs c) m) => m Int
getNumberOfUnsolvedNodes = length <$> getUnsolvedNodes

isLeaf :: (MonadState (Forest bs c) m) => NodeId -> m Bool
isLeaf nodeId = do
  (M.lookup nodeId <$> use children) >>= \case
    Nothing -> return False
    Just (NodeLeaf{}) -> return True
    Just (NodeBranch _ _) -> return False


-- | Check if the first node is a descendant of the second. 
--   O(n²)
isDescendantOf :: (MonadState (Forest bs c) m) => NodeId -> NodeId -> m [[NodeId]]
nodeId `isDescendantOf` b =
  if nodeId == b then
    return [[b]] 
  else
    lookupNode nodeId >>= \case
      Nothing -> return []
      Just (NodeLeaf{}) -> return []
      Just (NodeBranch _ cs) -> map (b:) <$> nodeId `isDescendantOfAny` cs

isDescendantOfAny :: (MonadState (Forest bs c) m) => NodeId -> [NodeId] -> m [[NodeId]]
nodeId `isDescendantOfAny` cs = mconcat <$> mapM (nodeId `isDescendantOf`) cs

data WithLeavesResult bs c = LeafNoOp
                           | LeafRelabel bs 
                           | LeafBranch NodeIds

-- | Perform an action on each leaf. These actions may modify the graph themselves.
--   These actions return an action that is performed on each leaf.
--
--   Note that the actions may alter the tree, but they should not alter the
--   leaf that is passed as first parameter.
--

withLeaves :: forall c bs m. (MonadState (Forest bs c) m, MonadError [NodeId] m) =>
              (NodeId -> bs -> c -> m (WithLeavesResult bs c)) -> m Natural
withLeaves f =
     -- Get the leaves in inverse-identifier order
     sum <$> (getLeafIds >>=
                          mapM (\nodeId ->
                               -- The lookup must be redone in case some leaves were solved already
                               (M.lookup nodeId <$> use children) >>= \case
                                  Nothing             -> return 0
                                  Just (NodeBranch {}) -> return 0
                                  Just (NodeLeaf constr bs)   -> -- It is still a leaf, carry on
                                   f nodeId bs constr >>= \case
                                     LeafNoOp         -> return 0
                                     LeafRelabel bs'  -> upsertLeaf nodeId bs' constr   >> return 0
                                     LeafBranch  cs   -> branchLeaf nodeId constr cs >> return 1))

uniq :: (Eq a) => [a] -> [a]
uniq [] = []
uniq (a:b:cs) | a == b = a:uniq' a cs
  -- Use an auxiliary function to make this lazier
  where uniq' a (a':cs) | a == a' = uniq' a cs
        uniq' _ cs                = uniq    cs
uniq (a:cs)            = a:uniq cs

revSort ::  (Ord a) => [a] -> [a]
revSort = sortBy (flip compare)
