{-|
Module      : Control.Freedom.Deconstruction
Description : Tools for deconstructing free structures.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)

In Control.Freedom.Construction, we give the tools for building
freedom datatypes. Here, we give the tools for deconstructing them, or
essentially pattern matching on them, which allows us to define functions
on sums from functions on summands. Just as a total function on typical
Haskell datatypes requires an exhaustive pattern match, total functions on
freedom datatypes requires a function for each summand of the sum.

Functions on individual summands are straightforward. Here's one which
just strips the @Pure@ constructor to give a function:

  @
    pure :: Pure h s t ~> (->) s t
    pure = \term -> case term of
        Pure f -> f
  @

This one allows us to substitute any value for a @None h s t@:

  @
    none :: x -> None h s t -> x
    none = \x term -> case term of
        None -> x

To write functions on our sum types, we bundle a function for each
summand (in that same order) with common codomain.
Here's a freedom-style @Maybe@ type, and an implementation of a function
similar to @maybe :: r -> (t -> r) -> Maybe t -> r@ from Prelude:

  @
    type FMyMaybe = Pure + None
    type MyMaybe = Fix FMyMaybe

    myMaybeInterpreter :: r -> (t -> r) -> (FMyMaybe h s t ~> ((->) s r))
    myMaybeInterpreter deflt f =
          (fmap f . pure)
        % (none (const deflt))
  @

To discharge the @~>@ type, use @function@.
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}

module Control.Freedom.Deconstruction (

      type (%)
    , (%)
    , Function
    , function
    , type (~>)

    ) where

import Prelude hiding (id, (.), pure)
import Control.Freedom.Construction
import Control.Category
import Control.Arrow
import Data.Profunctor

infixr 8 %
type int1 % int2 = (int1, int2)

(%) = (,)

class Function i domain range | i -> domain, i -> range where
    function :: i -> domain -> range

instance Function (domain -> range) domain range where
    function = id

instance
    ( Function i (f1 h s t) range
    , Function j (f2 h s t) range
    ) => Function (i % j) ((f1 + f2) h s t) range
  where
    function (left, right) = \sumTerm -> case sumTerm of
        FSumL term -> function left term
        FSumR term -> function right term

type family F (domain :: *) (range :: *) where
    F ((f1 + f2) h s t) g = (f1 h s t -> g, F (f2 h s t) g)
    F f1 g = (f1 -> g)

-- Almost a function. @a ~> b@ can give an @a -> b@ via @function@. The
-- definition of the type family @F@ guarantees that the Function class
-- constraint will always be met.
infixl 1 ~>
type domain ~> range = F domain range
