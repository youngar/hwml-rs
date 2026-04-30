{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS -fwarn-incomplete-patterns #-}
-- | Keeping track of unification history
module Tog.Unify.History (History'(..), Rendered(..), render, writeHistory) where

import Tog.Unify.Core
import Tog.Term.Core

import Tog.Names
import qualified Tog.PrettyPrint                  as PP

import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Foldable (toList)
import qualified Data.Map as Map
import Tog.Prelude hiding (writeFile)

import Data.Aeson (ToJSON(..))
import Data.Aeson.Encode.Pretty (encodePretty',Config(..),keyOrder,defConfig)
import System.IO.Temp (emptyTempFile)
import Data.ByteString.Lazy (writeFile)

import qualified Data.Text as T
import Data.Monoid (Sum(..))

data History' ec uc =
    -- | Constraints coming directly from the elaborator
    Elaborator {
      constraint     :: PP.Doc
     ,elabConstraint :: ec 
     ,constrLoc      :: SrcLoc
     ,children       :: Seq ConstraintId
     ,time           :: Double
     }
  |
    -- | Constraints that have been refined
    Refined {
     constrId   :: ConstraintId
    ,constrLoc  :: SrcLoc
    ,constraint :: PP.Doc
    ,termConstraint :: uc 
    ,children   :: Seq ConstraintId
    ,time       :: Double
    }
    -- | Constraints that come from new meta notifications
  | HistoryMeta {
     metaId    :: Int
    ,metaLoc   :: SrcLoc
    ,children  :: Seq ConstraintId
    ,time      :: Double
    }
    -- | Constraints that are still blocked 
  | Blocked {
     constrId   :: ConstraintId
    ,constrLoc  :: SrcLoc
    ,constraint :: PP.Doc
    ,termConstraint :: uc 
    ,waitingFor :: Seq ConstraintId
    ,blockedBy  :: PP.Doc
    }



getChildren :: History' ec uc -> Seq ConstraintId
getChildren Elaborator{children} = children
getChildren HistoryMeta{children} = children
getChildren Refined{children} = children
getChildren Blocked{} = mempty

data Status = Solved
            | Unsolved
            | WaitingFor (Seq ConstraintId)
            | BlockedBy Text
            deriving (Generic)

instance ToJSON Status

instance Monoid Status where
  mempty             = Solved

instance Semigroup Status where
  Solved <> y = y
  x <> Solved = x
  _ <> _      = Unsolved

data Rendered' text =
    RenderRoot {
      constrLoc    :: SrcLoc
    , status       :: Status
    , constraint   :: Text
    , termConstraint :: text
    , timeAcc      :: Double
    , timeSelf     :: Double
    , children     :: Seq (Rendered' text)
    }
  | RenderConstraint {
      constrLoc       :: SrcLoc
    , constrId     :: ConstraintId
    , status       :: Status
    , constraint   :: Text
    , termConstraint :: text
    , timeAcc      :: Double
    , timeSelf     :: Double
    , children     :: Seq (Rendered' text)
    }
  | RenderMissing {
      constrId :: ConstraintId
    } deriving (Generic, Functor, Foldable, Traversable)

type Rendered = Rendered' Text

instance ToJSON Rendered where

render :: forall t ec uc m. (PrettyM t ec, PrettyM t uc, MonadTerm t m) =>
          Seq (History' ec uc)
       -> m [Rendered]
render history = sequence $ map (traverse id) $ 
  [ let ((status, Sum timeAcc), childrenRendered) = goAll children in
    RenderRoot{
       constrLoc
      ,constraint = renderForJSON constraint
      ,termConstraint = renderForJSON <$> prettyM_ elabConstraint
      ,status
      ,children = childrenRendered 
      ,timeSelf = time
      ,timeAcc  = time + timeAcc 
      }
  | Elaborator{..} <- toList history
  ] ++
  [ let ((status, Sum timeAcc), childrenRendered) = goAll children in
    RenderRoot{
       constrLoc = metaLoc
      ,constraint = "New meta: " <> (T.pack$ show metaId)
      ,termConstraint = pure "-"
      ,status
      ,children = childrenRendered 
      ,timeSelf = time
      ,timeAcc  = time + timeAcc 
      }
  | HistoryMeta{..} <- toList history
  ]
  where
    historyMap = Map.fromList$ mconcat [
      case c of
        Elaborator{} -> []
        HistoryMeta{} -> []
        Refined{constrId} -> [(constrId, c)]
        Blocked{constrId} -> [(constrId, c)]
      | c <- toList history
      ]

    goAll :: Seq ConstraintId -> ((Status, Sum Double), Seq (Rendered' (m Text)))
    goAll cids = Seq.sortBy (compare `on` (\case
                                          RenderRoot{constrLoc} -> (Just constrLoc,Nothing)
                                          RenderConstraint{constrLoc,constrId} -> (Just constrLoc, Just constrId)
                                          RenderMissing{constrId} -> (Nothing, Just constrId)
                                      )) <$> traverse go cids

    go :: ConstraintId -> ((Status, Sum Double), (Rendered' (m Text)))
    go constrId = case Map.lookup constrId historyMap of
                Nothing           -> pure$ RenderMissing{constrId}
                Just Elaborator{} -> error "Elaborator has no constrId"
                Just HistoryMeta{} -> error "Meta constraint has no constrId"
                Just Refined{constrLoc,constrId,constraint,termConstraint,children,time}  -> do
                  tell (mempty, Sum time)
                  (childrenRendered, (status, Sum timeAcc)) <- listen$ traverse go children
                  pure$ RenderConstraint{constrLoc, constrId
                                        ,constraint = renderForJSON constraint
                                        ,termConstraint = renderForJSON <$> prettyM_ termConstraint
                                        ,status
                                        ,children = childrenRendered
                                        ,timeSelf = time
                                        ,timeAcc  = time + timeAcc
                                        }

                Just Blocked{..}  -> do
                  tell (Unsolved, Sum 0)
                  pure RenderConstraint{constrLoc,constrId
                                       ,constraint = renderForJSON constraint
                                       ,termConstraint = renderForJSON <$> prettyM_ termConstraint
                                       ,status =
                                            case waitingFor of
                                              [] -> BlockedBy $ renderForJSON blockedBy
                                              _  -> WaitingFor waitingFor
                                       ,children = []
                                       ,timeSelf = 0
                                       ,timeAcc  = 0
                                       }

renderForJSON :: PP.Doc -> Text
renderForJSON doc = T.pack$ PP.render doc {- >>= \case
  '\n' -> [' ']
  c    -> [c]-}

writeHistory :: [Rendered] -> IO FilePath
writeHistory contents = do
  f <- emptyTempFile "." "history-.json"
  writeFile f (encodePretty' defConfig{
                  confCompare = keyOrder [
                       "tag"
                      ,"constrId"
                      ,"constraint"
                      ,"termConstraint"
                      ,"timeSelf"
                      ,"timeAcc"
                      ,"status"
                      ]} contents)
  return f
