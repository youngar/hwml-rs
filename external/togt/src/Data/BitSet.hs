module Data.BitSet
       (module Data.ISet
       ,BitSet
       ,empty
       ,member
       ,singleton
       ,insert
       ,null
       ,fromList
       ,isSubsetOf
       ,size
       ,intersect
       ,union
       ,toListF, toList
       ,integerAction
       ,safeIntegerAction)
       where

import Prelude hiding (null)
import Data.ISet(ISetMember(..), ISetMemberM(..))
import Data.Bits
import Data.Function
import Numeric.Natural
import Data.Hashable

-------------
-- Bit set --
-------------

-- A simpler representation of integer sets. Equivalent to Data.BitSet for
-- small sets (elements in the range 0..29), slower for sets involving
-- larger elements.
newtype BitSet a = BitSet { bSet :: Natural } deriving (Eq, Hashable)

instance Semigroup (BitSet a) where (<>) = union
instance Monoid (BitSet a) where mempty  = empty

empty :: BitSet a
empty = BitSet zeroBits

member :: (ISetMember a) => a -> BitSet a -> Bool
member k (BitSet s) = testBit s (repr k)

singleton :: (ISetMember a) => a -> BitSet a 
singleton = BitSet . bit . repr

insert :: (ISetMember a) => a -> BitSet a -> BitSet a 
insert k (BitSet s) = BitSet$ setBit s (repr k)

null :: BitSet a -> Bool 
null = (== zeroBits) . bSet

fromList :: (ISetMember a) => [a] -> BitSet a
fromList =  BitSet . fromBitsList . map repr

isSubsetOf :: BitSet a -> BitSet a -> Bool 
a `isSubsetOf` b = (a `union` b) == b

size :: BitSet a -> Int
size = popCount . bSet

intersect :: BitSet a -> BitSet a -> BitSet a
intersect = (BitSet.) . (.&.) `on` bSet

union :: BitSet a -> BitSet a -> BitSet a
union = (BitSet.) .  (.|.) `on` bSet

overlap :: BitSet a -> BitSet a -> Bool
overlap = ((not.null).) . (BitSet.) . (.&.) `on` bSet

toListF :: (Applicative t, ISetMemberM t a) => BitSet a -> [t a]   
toListF = map full . toBitsList . bSet

toList :: (Applicative t, ISetMemberM t a) => BitSet a -> t [a]   
toList = traverse full . toBitsList . bSet

-- | Increment or decrement all numbers  in the set
integerAction :: Int -> BitSet a -> BitSet a
integerAction k (BitSet a) = BitSet$ a `shift` k

-- | Increment or decrement all numbers  in the set
safeIntegerAction :: Int -> BitSet a -> Maybe (BitSet a)
safeIntegerAction k (BitSet a) =
  let res = a `shift` k in
  if  res `shift` (-k) == a then
    Just (BitSet res)
  else
    Nothing

--- Internal functions ---
toBitsList :: Bits a => a -> [Int]
toBitsList a = go (popCount a) 0
  where
    go :: Int -> Int -> [Int]
    go 0 _ = []
    go n k | testBit a k   = k:go (n-1) (k+1)
    go n k | otherwise     =   go  n    (k+1)
  
fromBitsList :: Bits a => [Int] -> a
fromBitsList = foldr (flip setBit) zeroBits

                   
