{-|
Module      : Control.Freedom.Construction
Description : Construction of (E)DSLs from small parts.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)

This module provides infrastructure for building free structures from
singleton datatypes of a certain kind, namely

    @
      (* -> * -> *) -> * -> * -> *
    @

They can be mixed via the type (+). The type

    @
      f + g
    @

is the disjoint union of the constructors of @f@ and @g@, and it as well has
kind @(* -> * -> *) -> * -> * -> *@

To make use of these types, we also provide the newtype @Fix@, where
@Fix f@ feeds @f@ back into itself to obtain a @* -> * -> *@.

To avoid the unwieldly juggling of (+) constructors, we also give the classes
necessary to implement

    @
      inj :: Inject2 f g => f (Fix g) s t -> Fix g s t
    @

which is very useful for writing terms of @Fix f s t@.

-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE Arrows #-}

module Control.Freedom.Construction (

      Fix(..)
    , inj
    , Inject2

    ) where

import Prelude hiding ((.), id)
import Control.Category
import Data.Proxy

data FSum (f :: (* -> * -> *) -> * -> * -> *) (g :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    FSumL :: (f h) s t -> FSum f g h s t
    FSumR :: (g h) s t -> FSum f g h s t

infixr 8 +
type f + g = FSum f g

class Inject2Single (f :: (* -> * -> *) -> * -> * -> *) (g :: (* -> * -> *) -> * -> * -> *) where
    inject2Single :: f hs a b -> g hs a b

instance Inject2Single f f where
    inject2Single = id

instance {-# OVERLAPS #-} Inject2Single f (f + h) where
    inject2Single = FSumL

instance {-# OVERLAPS #-} (Inject2Single f h) => Inject2Single f (g + h) where
    inject2Single = FSumR . inject2Single

class Inject2Multiple (f :: (* -> * -> *) -> * -> * -> *) (g :: (* -> * -> *) -> * -> * -> *) where
    inject2Multiple :: f hs a b -> g hs a b

instance (Inject2Single f h) => Inject2Multiple f h where
    inject2Multiple = inject2Single

instance
    ( Inject2Single f h
    , Inject2Multiple g h
    ) => Inject2Multiple (f + g) h
  where
    inject2Multiple term = case term of
        FSumL x -> inject2Single x
        FSumR x -> inject2Multiple x

data FSumType = FSumSingle | FSumMultiple

type family FSumIndicator (f :: (* -> * -> *) -> * -> * -> *) :: FSumType where
    FSumIndicator (g + h) = 'FSumMultiple
    FSumIndicator g = 'FSumSingle

class Inject2' (indicator :: FSumType) (f :: (* -> * -> *) -> * -> * -> *) (g :: (* -> * -> *) -> * -> * -> *) where
    inject2' :: Proxy indicator -> f hs a b -> g hs a b

instance Inject2Single f g => Inject2' 'FSumSingle f g where
    inject2' _ = inject2Single

instance Inject2Multiple f g => Inject2' 'FSumMultiple f g where
    inject2' _ = inject2Multiple

class Inject2 (f :: (* -> * -> *) -> * -> * -> *) (g :: (* -> * -> *) -> * -> * -> *) where
    inject2 :: f hs a b -> g hs a b

instance Inject2' (FSumIndicator f) f g => Inject2 f g where
    inject2 = inject2' (Proxy :: Proxy (FSumIndicator f))

newtype Fix f s t = Fix {
      runFix :: f (Fix f) s t
    }

inj :: Inject2 f g => f (Fix g) a b -> Fix g a b
inj = Fix . inject2
