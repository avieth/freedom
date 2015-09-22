{-|
Module      : 
Description : 
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

import Control.Freedom.Construction
import Control.Freedom.Deconstruction

type SourceID = Int
type Frequency = Double

type FMyDSL = Amplify Rec + Filter Pure Rec + Source
type MyDSL = Fix FMyDSL

data Source h s t where
    Source :: h () SourceID -> Source h () ()

data Amplify f h s t where
    Amplify :: f h () () -> Amplify f h () ()

data Filter f g h s t where
    Filter :: f h () Frequency -> g h () () -> Filter f g h () ()

countFilters :: MyDSL () () ~> (Int -> Int)
countFilters = countFiltersAmplify
             % countFiltersFilter
             % countFiltersSource
  where

    countFiltersAmplify :: Amplify f h () () -> Int -> Int
    countFiltersAmplify = const id

    countFiltersFilter :: Filter f g h () () -> Int -> Int
    countFiltersFilter = const ((+) 1)

    countFiltersSource :: Source h () () -> Int -> Int
    countFiltersSource = const id

filterCount :: MyDSL () () -> Int
filterCount term = function (Xif countFilters) term 0
