{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Tog.Test.Config (
    module Tog.Test.Config
   ,(<>)
   )
   where

import Tog.Test.Utils.DashDash
import Data.Semigroup
import Data.Function

type TogConf = DashDash

data Configuration = Configuration {
   configName :: String 
 , config     :: DashDash
 }

instance Eq Configuration where                     
  (==) = (==) `on` config

instance Ord Configuration where
  compare = compare `on` configName

defaults = Configuration "default"$
          defaultTestConf <> dd     "synEquality" "2"
                          <> ddYes  "physicalEquality"
                          <> dd     "termType" "S"
                          <> dd     "solver"   "S"
                          <> ddYes  "checkMetaConsistency"
                          <> ddYes  "audit"

with_S = Configuration "S"$
         config defaults <> dd "solver" "S"

with_S_HC3 = Configuration "S,HC3" $
             config with_S <> dd "termType" "HC3"

with_T = Configuration "T"$
         config defaults <> dd "solver" "T"

with_W = Configuration "W"$
         config defaults <> dd "solver" "W"
                         <> ddNo "nfInUnifier"

with_T_HC3 = Configuration "T,HC3"$
             config with_T <> dd "termType" "HC3"

and_P = Configuration "P"$
         mempty <> dd "termType" "P"

and_PH = Configuration "PH"$
         mempty <> dd "termType" "PH"

and_HC4P = Configuration "HC4P"$
         mempty <> dd "termType" "HC4P"

and_HC3 = Configuration "HC3"$ mempty
          <> dd "termType" "HC3"
 
and_HC4 = Configuration "HC4"$ mempty
          <> dd "termType" "HC4"

and_HC2 = Configuration "HC2"$ mempty
          <> dd "termType" "HC2"
 
and_noCheck = Configuration "~chk"$ mempty
                <> ddNo  "checkMetaConsistency"

and_noSynEq = Configuration "~syn"$ mempty
                <> dd    "synEquality" "0"

and_noNf    = Configuration "~nf"$ mempty
                <> ddNo  "nfInUnifier"

and_Nf    = Configuration "nf"$ mempty
                <> ddYes  "nfInUnifier"

and_FE = Configuration "fe"$ mempty
                <> ddYes  "fastElaborate"

and_PHI = termType "PHI"

termType s = Configuration s$ mempty
             <> dd "termType" s

and_noFastEq = Configuration "noFastEq" $ mempty
                    <> ddNo   "physicalEquality"
                    <> dd     "synEquality" "0"

and_pCurry = Configuration "pCurry" $ mempty
                    <> ddYes "paranoidContextCurrying"

-- | Optimizations that increase speed at the cost of hiding bugs
and_fastLoose = Configuration "fast"$ mempty
                  <> ddNo   "checkMetaConsistency"
                  <> ddYes  "noCheckElaborated"
                  <> ddNo   "audit"

instance Semigroup Configuration where
  a <> b = Configuration (configName a <> ";" <> configName b)
                         (config a <> config b)

defaultTestConf = ddYes "quiet"

and_stats = Configuration "stats"$ mempty
              <> ddYes "stats"
