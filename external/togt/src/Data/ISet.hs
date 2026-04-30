module Data.ISet (
  ISet,
  ISetMember(..),
  ISetMemberM(..),
  empty,
  member,
  insert,
  delete,
  singleton,
  toList,
  toListF,
  null,
  fromList,
  isSubsetOf,
  overlap,
  size,
  mapMonotonic,
  reprSet,
  union,
  unsafeFromReprSet) where

import Prelude hiding (null)
import Data.Semigroup
import qualified Data.IntSet as IS
import Data.Function (on)

import Numeric.Natural (Natural)

-- | Sets of things that are integers up to equality and hashing

newtype ISet a = ISet { iSet :: IS.IntSet }
                 deriving (Monoid, Semigroup, Show, Eq, Ord)

-- | Sets of things that can be members of ISet
--     
--   prop>  repr a == repr b  ⇔   a == b     
class ISetMember a where
  repr    :: a -> Int

instance ISetMember Natural where repr = fromIntegral
instance ISetMember Int where repr = id
instance (Applicative f) => ISetMemberM f Natural where full = pure . fromIntegral

-- | How to extract a member from an ISet
--
--   prop> (== a) <$> full (repr a)   ≡   const True <$> full (repr a) 
class (Functor f, ISetMember a) => ISetMemberM f a where  
  full    :: Int -> f a

empty :: ISet a
empty = mempty

member :: (ISetMember a) => a -> ISet a -> Bool
member k (ISet s) = IS.member (repr k) s

(\\) :: (ISetMember a) => ISet a -> ISet a -> ISet a
(\\) = (ISet .) . ( (IS.\\) `on` iSet)

toListF :: (Applicative t, ISetMemberM t a) => ISet a -> [t a]   
toListF = map full . IS.toList . iSet

toList :: (Applicative t, ISetMemberM t a) => ISet a -> t [a]   
toList = traverse full . IS.toList . iSet

singleton :: (ISetMember a) => a -> ISet a 
singleton = ISet . IS.singleton . repr

insert :: (ISetMember a) => a -> ISet a -> ISet a 
insert k (ISet s) = ISet$ IS.insert (repr k) s

delete :: (ISetMember a) => a -> ISet a -> ISet a 
delete k (ISet s) = ISet$ IS.delete (repr k) s

null :: ISet a -> Bool 
null = IS.null . iSet

fromList :: (ISetMember a) => [a] -> ISet a
fromList =  ISet . IS.fromList . map repr

union :: (ISetMember a) => ISet a -> ISet a -> ISet a
union = (ISet .) . IS.union `on` iSet

isSubsetOf :: ISet a -> ISet a -> Bool 
isSubsetOf = IS.isSubsetOf `on` iSet

overlap :: ISet a -> ISet a -> Bool 
overlap = (not .) . IS.disjoint `on` iSet

size :: ISet a -> Int
size = IS.size . iSet

mapMonotonic :: (ISetMemberM f a, Applicative f) => (a -> a) -> ISet a -> f (ISet a)
mapMonotonic f = fmap (ISet . IS.fromAscList . map (repr . f)) . traverse full . IS.toAscList . iSet

reprSet :: ISet a -> IS.IntSet 
reprSet = iSet

unsafeFromReprSet :: IS.IntSet -> ISet a
unsafeFromReprSet = ISet

