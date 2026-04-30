module Tog.Test.Utils.DashDash (
  -- * Building
    dd, ddYes, ddNo, ddPos, dashDash, DashDash, DashDashName
  -- * Querying
  , getParam, getPos, getFlag
  ) where

import Data.Semigroup
import Data.String (IsString(..))
import Data.Maybe (listToMaybe)
import Data.List (sort)
import Data.Function (on)
import Generics.Deriving.Show (GShow(..))
import GHC.Generics

import Data.Aeson (ToJSON(..), FromJSON, genericToEncoding, defaultOptions)
import Safe (atMay)

data DashDashName = Long  String
                  | Short Char
                  deriving (Eq, Show, Generic, Ord)

instance GShow DashDashName where
instance ToJSON DashDashName where
instance FromJSON DashDashName where


data DashDashElem where
  DDParam :: { ddName  :: DashDashName, ddValue :: String } -> DashDashElem
  DDFlag  :: { ddName  :: DashDashName, ddOn :: Bool } -> DashDashElem
  DDPos   :: { ddValue :: String } -> DashDashElem 
  deriving (Show, Generic, Eq, Ord)

instance GShow DashDashElem where
instance ToJSON DashDashElem where
instance FromJSON DashDashElem where

newtype DashDash = DD { toReversedList :: [DashDashElem] } deriving (Generic)
instance GShow DashDash where

instance Eq DashDash where
  (==) = (==) `on` (sort . toReversedList . removeSuperseding)

instance Show DashDash where
  show = gshow . removeSuperseding
  showsPrec p = gshowsPrec p . removeSuperseding

instance ToJSON DashDash where toEncoding = genericToEncoding defaultOptions . removeSuperseding
instance FromJSON DashDash where

instance Semigroup DashDash where
  DD a <> DD b = DD (b <> a)

-- Reverse append monoid
instance Monoid DashDash where                   
  mempty = DD mempty
  mappend = (<>)

instance IsString DashDashName where
  fromString ('-':'-':str) = Long str
  fromString ('-':c:[]) = Short c
  fromString [c] = Short c
  fromString str = Long str

dd :: DashDashName -> String -> DashDash 
dd name value = DD$ [DDParam{ddName=name,ddValue=value}]

ddYes, ddNo :: DashDashName -> DashDash 
ddYes name = DD$ [DDFlag name True]
ddNo  name = DD$ [DDFlag name False]

ddPos :: String -> DashDash
ddPos value = DD [DDPos value]

supersedes :: DashDashElem -> DashDashElem -> Bool
supersedes DDParam{ddName=n1} DDParam{ddName=n2} = n1 == n2
supersedes DDFlag{ddName=n1}  DDFlag{ddName=n2}  = n1 == n2
supersedes _                  _                  = False

-- | Complexity is O(n²). Could do better.
removeSuperseding :: DashDash -> DashDash
removeSuperseding DD{toReversedList} = DD{toReversedList = go toReversedList}
  where
  go = \case
    []      -> []
    (e:es)  -> e:go (filter (not . (e `supersedes`)) es)

dashDashName :: DashDashName -> String
dashDashName (Long str) = "--" ++ str
dashDashName (Short c)  = "-" ++ [c]

-- | Renders a command-line as command-line arguments. 
dashDash :: (IsString a) => DashDash -> [a]
dashDash dd =
  map fromString$ concat$ map dashDashElem$ reverse$ toReversedList$ removeSuperseding dd
  where
    dashDashElem :: DashDashElem -> [String]
    dashDashElem = \case
       DDParam{ddName=ddName@Long{},ddValue}      -> [dashDashName ddName, ddValue]
       DDParam{ddName=ddName@Short{},ddValue}     -> [dashDashName ddName ++ ddValue]
       DDFlag{ddName,ddOn = True}                 -> [dashDashName ddName]
       DDFlag{ddOn = False}  -> []
       DDPos{ddValue}                             -> [ddValue]

getParam :: DashDash -> DashDashName -> Maybe String
dd `getParam` needle = listToMaybe [ddValue | DDParam{ddName,ddValue} <- toReversedList dd, ddName == needle]

getPos :: DashDash -> Int -> Maybe String
dd `getPos` needle = reverse [ddValue | DDPos{ddValue} <- toReversedList dd] `atMay` needle

getFlag :: DashDash -> DashDashName -> Maybe Bool
dd `getFlag` needle = listToMaybe [ddOn | DDFlag{ddName,ddOn} <- toReversedList dd, ddName == needle]


