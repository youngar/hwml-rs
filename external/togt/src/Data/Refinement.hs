-- | Data structure that keeps track of how elements are refined into one another
--   over the execution of a program. 
-- 
--   If an element refines into no elements, it is considered solved. This
--   condition is propagated upwards.
--



module Data.Refinement (
   Refinement
  ,empty
  ,branch
  ,isSolved
  ,areAllSolved
  ,hasChildren
  ,countSolved
  ,countPending
  ,countAll
  ,unsolvedChildren
  ,unsolvedChildrenN
  )
where

import Data.List (foldl')
import qualified Data.IntSet      as IS
import qualified Data.IntMap as IM
import Data.IntMap (IntMap)
import Data.ISet (ISet, ISetMember(..), reprSet, ISetMemberM(..))
import qualified Data.ISet as I

-- `IntMap`s are strict internally
data Status a = Fresh { parent :: !Int }
                -- A node which is waiting on zero or more children
              | Waiting { parent :: !Int, children :: !IS.IntSet }
                -- A node with no parents
              | Root { children :: !IS.IntSet }
              deriving (Show)

-- | Invariant: Elements of solved are not in pending, and viceversa
--   Invariant: The `children` field of elements in `pending` are contained in pending.
--   Invariant: The `children` field of elements in `pending` is non-empty.
--
--   The fields are strict. Forcing will prevent old copies from being kept in memory.
data Refinement a = Refinement{
      solved  :: !IS.IntSet
    , pending :: !(IntMap (Status a))
    } deriving (Show)

empty :: Refinement a
empty = Refinement IS.empty IM.empty

-- | Adds a new node with some number of children.
--
--   Complexity: Amortized O(n)
--
--   The node does not need to be in the tree already. If it
--   is, it should be in fresh state.
branch :: ISetMember a => a -> [a] -> Refinement a -> Refinement a 
branch p cs r = go (repr p) (IS.fromList (fmap repr cs) IS.\\ solved r) r
  where
    -- This is the step adds branches to the tree
    -- If a node is refined into having no children,
    -- it is added to the solved list.
    -- If it has a parent, it's list of children is updated to remove
    -- the solved child.
    go :: Int -> IS.IntSet -> Refinement a -> Refinement a 
    go p cs = do
      (IM.lookup p <$> pending) >>= \case
        Nothing | IS.null cs -> markSolved p
                | otherwise  -> addNode p Root{ children = cs } . addFresh p cs
                                           
        Just Fresh { parent = gp } | IS.null cs -> removeChild gp p . markSolved p . forgetNode p
                                   | otherwise  -> addNode p Waiting{ parent = gp, children = cs } . addFresh p cs

        Just _ -> error "Applied `branch` more than once on the same node"

    addNode cid status r = r{pending = IM.insert cid status (pending r)}
    updateNode = addNode

    markSolved cid r = r{solved = IS.insert cid (solved r)}

    forgetNode cid r = r{pending = IM.delete cid (pending r)}

    removeChild p cid = do
       IM.lookup p <$> pending >>= \case
         Just Root{children=(IS.delete cid -> cs')}
           | IS.null cs' -> markSolved p . forgetNode p
           | otherwise   -> updateNode p Root{children=cs'} 

         Just Waiting{parent = gp, children=(IS.delete cid -> cs')}
           | IS.null cs' -> removeChild gp p . markSolved p . forgetNode p
           | otherwise   -> updateNode p Waiting{parent = gp, children = cs'} 

         _ ->  error "Internal error"

    addFresh p cs r = r{pending = foldl' (flip$ flip IM.insert (Fresh p)) (pending r) (IS.toList cs)}

-- | Is solved
--   Says yes iff a node has no children, or all the nodes have no children.
--   Complexity: O(1)
isSolved :: ISetMember a => a -> Refinement a -> Bool
isSolved a Refinement{solved} = IS.member (repr a) solved

-- | Check if a node is waiting on children
hasChildren :: ISetMember a => a -> Refinement a -> Bool
hasChildren p Refinement{pending} =
  case IM.lookup (repr p) pending of
    Nothing   -> False
    Just Fresh{}   -> False
    Just Waiting{} -> True
    Just Root{}    -> True

-- | Is solved
--   Says yes iff a node has no children, or all the nodes have no children.
--   Complexity: O(m)
areAllSolved :: ISetMember a => ISet a -> Refinement a -> Bool
areAllSolved as Refinement{solved} = reprSet as `IS.isSubsetOf` solved

-- | Get unsolved children
unsolvedChildren   ::  forall a. ISetMember a => a      -> Refinement a -> ISet a
unsolvedChildrenN  ::  forall a. ISetMember a => ISet a -> Refinement a -> ISet a
unsolvedChildren   =   flip $ fst . unsolvedChildren_
unsolvedChildrenN  =   flip $ snd . unsolvedChildren_

unsolvedChildren_ :: ISetMember a => Refinement a -> (a -> ISet a, ISet a -> ISet a)
unsolvedChildren_ Refinement{pending} = (go' , gos')
  where
  go'  = I.unsafeFromReprSet . go  . repr
  gos' = I.unsafeFromReprSet . gos . I.reprSet

  go :: Int -> IS.IntSet
  go p = 
    let i = repr p in
    case IM.lookup i pending of
      Nothing                 -> mempty
      Just Fresh{}            -> IS.singleton i
      Just Waiting{children}  -> gos children
      Just Root{children}     -> gos children

  gos = mconcat . map go . IS.toList   

-- | Number of solved elements
countSolved :: Refinement a -> Int
countSolved = IS.size . solved

-- | Count pending
countPending :: Refinement a -> Int
countPending = IM.size . pending

-- | Count all
countAll :: Refinement a -> Int
countAll = (+) <$> countSolved <*> countPending
