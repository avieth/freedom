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

Since @Fix f@ is defined here, and since we would like variations of @Fix f@ to
be instances of @Functor@, @Profunctor@, @Applicative@, @Alternative@, @Arrow@,
@ArrowChoice@, @Monad@ and others, depending upon the summands present in
@f@, we also define many relevant datatypes here--the datatype which must be
present in @f@ in order to achieve the relevant instances in @Fix f@. Defining
them in other modules would yield orphan instances.

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

      type (+)
    , FSum(..)
    , Fix(..)
    , inj
    , Inject2
    , inject2

    , Rec(..)
    , Close(..)
    , Pure(..)
    , None(..)
    , Dimap(..)
    , Dot(..)
    , Id(..)
    , Sequence(..)
    , type (×)
    , (×)
    , Arr(..)
    , First(..)
    , Apply(..)
    , Alternative(..)
    , Join(..)

    ) where

import Prelude hiding ((.), id)
import Control.Category
import Control.Applicative hiding (Alternative)
import qualified Control.Applicative as Applicative
import Control.Arrow
import Data.Proxy
import Data.Profunctor

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

-- Would be nice to have
--
--   @inj' :: Fix f s t -> Fix g s t@
--
-- whenever @f@ is a sub-sum of @g@ (every @f@ summand is in @g@).
--
-- Is this possible? We runFix to get an @f (Fix f) s t@ and we must somehow
-- recursively @inject2@ each @f@-term into @g@ to recover @g (Fix g)@.
-- The issue is that @inject2@ demands the parameters @hs@ be the same for
-- both terms. What we need is
--
--   @ftrans :: (forall s t . h s t -> h' s t) -> f h s t -> f h' s t@
--
-- This is TODO; not *that* imporant, but desirable.
--
-- We'll want to use typeclasses to resolve this automatically... 

-- | When a @Rec@ is part of a @Fix@ed sum @f@, it represents any term of
--   @Fix f@.
data Rec (h :: * -> * -> *) (s :: *) (t :: *) where
    Rec :: h s t -> Rec h s t

-- | Close a datatype, so that it ignores the @h@ parameter. If you use a
--   @Close f@ in a sum @g@, then @Fix g@ does not include @f (Fix g)@.
data Close (f :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    Close :: Fix f s t -> Close f h s t

-- | When a @Pure@ is part of a @Fix@ed sum @f@, it represents any Haskell
--   function.
data Pure (h :: * -> * -> *) (s :: *) (t :: *) where
    Pure :: ((->) s t) -> Pure h s t

data None (h :: * -> * -> *) (s :: *) (t :: *) where
    None :: None h s t

data Dimap (f :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    Dimap :: (s -> s') -> (t' -> t) -> f h s' t' -> Dimap f h s t

data Id (h :: * -> * -> *) (s :: *) (t :: *) where
    Id :: Id h s s

data Dot (left :: (* -> * -> *) -> * -> * -> *) (right :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    Dot :: left h t u -> right h s t -> Dot left right h s u

data Sequence (left :: (* -> * -> *) -> * -> * -> *) (right :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    Sequence :: left h s () -> right h s t -> Sequence left right h s t

infixr 8 ×
type left × right = Sequence left right

(×) :: left h s () -> right h s t -> Sequence left right h s t
(×) = Sequence

data Arr (h :: * -> * -> *) (s :: *) (t :: *) where
    Arr :: (->) s t -> Arr h s t

data First (f :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    First :: f h s t -> First f h (s, c) (t, c)

data Apply (f :: (* -> * -> *) -> * -> * -> *) (g :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    Apply :: f h s (t -> u) -> g h s t -> Apply f g h s u

data Empty (h :: * -> * -> *) (s :: *) (t :: *) where
    Empty :: Empty h s t

data Alternative (f :: (* -> * -> *) -> * -> * -> *) (g :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    Alternative :: f h s t -> g h s t -> Alternative f g h s t

data Join (f :: (* -> * -> *) -> * -> * -> *) (g :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    Join :: f h s (g h s t) -> Join f g h s t

instance
    ( Inject2 (Dimap Rec) f
    ) => Profunctor (Fix f)
  where
    dimap l r term = inj (Dimap l r (Rec term))

instance
    ( Inject2 (Dimap Rec) f
    ) => Functor (Fix f s)
  where
    fmap = rmap

instance
    ( Inject2 Id f
    , Inject2 (Dot Rec Rec) f
    ) => Category (Fix f)
  where
    id = inj Id
    (.) left right = inj (Dot (Rec left) (Rec right))

instance
    ( Inject2 Pure f
    , Inject2 (Dimap Rec) f
    , Inject2 (Apply Rec Rec) f
    ) => Applicative (Fix f s)
  where
    pure = inj . Pure . const
    (<*>) left right = inj (Apply (Rec left) (Rec right))

instance
    ( Inject2 Pure f
    , Inject2 (Dimap Rec) f
    , Inject2 (Apply Rec Rec) f
    , Inject2 Empty f
    , Inject2 (Alternative Rec Rec) f
    ) => Applicative.Alternative (Fix f s)
  where
    empty = inj Empty
    (<|>) left right = inj (Alternative (Rec left) (Rec right))

instance
    ( Inject2 Id f
    , Inject2 (Dot Rec Rec) f
    , Inject2 Arr f
    , Inject2 (First Rec) f
    ) => Arrow (Fix f)
  where
    arr = inj . Arr
    first = inj . First . Rec

instance
    ( Inject2 Pure f
    , Inject2 (Dimap Rec) f
    , Inject2 (Apply Rec Rec) f
    , Inject2 (Join Rec Rec) f
    ) => Monad (Fix f s)
  where
    return = pure
    (>>=) x k = inj (Join (Rec (fmap (Rec . k) x)))
