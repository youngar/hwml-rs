{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS -Wwarn #-}
module Tog.Unify.Core (
  ConstraintId
  ) where

import           Tog.Prelude

type ConstraintId = Natural
