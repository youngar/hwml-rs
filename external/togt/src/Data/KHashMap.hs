module Data.KHashMap (
   KHashMap
  ,lookupWithKey
  ,lookupValue
  ,insertValue
  ,toListValues
  ,module HMS
  ) where

import Data.HashMap.Strict  as HMS
import Data.Hashable (Hashable)

type KHashMap k v = HMS.HashMap k (k, v)
lookupWithKey :: (Eq k, Hashable k) => k -> KHashMap k v -> Maybe (k, v)
lookupWithKey = HMS.lookup

lookupValue :: (Eq k, Hashable k) => k -> KHashMap k v -> Maybe v
lookupValue = (fmap snd.) . HMS.lookup

insertValue :: (Eq k, Hashable k) => k -> v -> KHashMap k v -> KHashMap k v
insertValue k v = HMS.insert k (k,v)

toListValues :: KHashMap k v -> [(k,v)]
toListValues = fmap snd . HMS.toList
