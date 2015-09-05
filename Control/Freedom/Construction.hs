{-|
Module      : Control.Freedom.Construction
Description : Definitions for construction of free structures.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}

module Control.Freedom.Construction (

      F2Sum(..)
    , type (+)
    , Fix(..)
    , inj

    , FProfunctor(..)
    , FCategory(..)
    , FApplicative(..)
    , FAlternative(..)
    , FArrow(..)
    , FArrowChoice(..)
    , FMonad(..)

    , ApArrow(..)
    , AltArrow(..)
    , KleisliArrow(..)

    ) where

import Prelude hiding (id, (.))
import qualified Prelude as P
import Control.Category
import Control.Arrow
import Control.Applicative
import Data.Profunctor
import Data.Proxy

data F2Sum (f :: (* -> * -> *) -> * -> * -> *) (g :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (a :: *) (b :: *) :: * where
    F2SumLeft :: (f h) a b -> F2Sum f g h a b
    F2SumRight :: (g h) a b -> F2Sum f g h a b

infixr 8 +
type (+) = F2Sum

class Inject2Single (f :: (* -> * -> *) -> * -> * -> *) (g :: (* -> * -> *) -> * -> * -> *) where
    inject2Single :: f h a b -> g h a b

instance Inject2Single f f where
    inject2Single = id

instance {-# OVERLAPS #-} Inject2Single f (f + h) where
    inject2Single = F2SumLeft

instance {-# OVERLAPS #-} (Inject2Single f h) => Inject2Single f (g + h) where
    inject2Single = F2SumRight . inject2Single

class Inject2Multiple (f :: (* -> * -> *) -> * -> * -> *) (g :: (* -> * -> *) -> * -> * -> *) where
    inject2Multiple :: f h a b -> g h a b

instance (Inject2Single f h) => Inject2Multiple f h where
    inject2Multiple = inject2Single

instance
    ( Inject2Single f h
    , Inject2Multiple g h
    ) => Inject2Multiple (f + g) h
  where
    inject2Multiple term = case term of
        F2SumLeft x -> inject2Single x
        F2SumRight x -> inject2Multiple x

data FSumType = FSumSingle | FSumMultiple

type family FSumIndicator (f :: (* -> * -> *) -> * -> * -> *) :: FSumType where
    FSumIndicator (g + h) = FSumMultiple
    FSumIndicator g = FSumSingle

class Inject2' (indicator :: FSumType) (f :: (* -> * -> *) -> * -> * -> *) (g :: (* -> * -> *) -> * -> * -> *) where
    inject2' :: Proxy indicator -> f h a b -> g h a b

instance Inject2Single f g => Inject2' FSumSingle f g where
    inject2' _ = inject2Single

instance Inject2Multiple f g => Inject2' FSumMultiple f g where
    inject2' _ = inject2Multiple

class Inject2 (f :: (* -> * -> *) -> * -> * -> *) (g :: (* -> * -> *) -> * -> * -> *) where
    inject2 :: f h a b -> g h a b

instance Inject2' (FSumIndicator f) f g => Inject2 f g where
    inject2 = inject2' (Proxy :: Proxy (FSumIndicator f))

newtype Fix (f :: (* -> * -> *) -> * -> * -> *) (s :: *) (t :: *) = Fix {
      unFix :: f (Fix f) s t
    }

inj :: Inject2 f g => f (Fix g) a b -> Fix g a b
inj = Fix . inject2

data FProfunctor (f :: * -> * -> *) (s :: *) (t :: *) where
    FProfunctorDimap :: (s -> t) -> (u -> v) -> f t u -> FProfunctor f s v

data FCategory (f :: * -> * -> *) (s :: *) (t :: *) where
    FCategoryId :: FCategory f t t
    FCategoryComp :: f b c -> f a b -> FCategory f a c

data FApplicative (f :: * -> * -> *) (s :: *) (t :: *) where
    FApplicativePure :: t -> FApplicative f s t
    FApplicativeAp :: f s (t -> u) -> f s t -> FApplicative f s u

data FAlternative (f :: * -> * -> *) (s :: *) (t :: *) where
    FAlternativeEmpty :: FAlternative f s t
    FAlternativePlus :: f s t -> f s t -> FAlternative f s t

data FArrow (f :: * -> * -> *) (s :: *) (t :: *) where
    FArrow :: (a -> b) -> FArrow f a b
    FFirst :: f a b -> FArrow f (a, c) (b, c)

data FArrowChoice (f :: * -> * -> *) (s :: *) (t :: *) where
    FLeft :: f a b -> FArrowChoice f (Either a c) (Either b c)

data FMonad (f :: * -> * -> *) (s :: *) (t :: *) where
    FMonadReturn :: t -> FMonad f s t
    FMonadBind :: f s t -> (t -> f s u) -> FMonad f s u

instance Inject2 FProfunctor f => Functor (Fix f a) where
    fmap f term = Fix (inject2 (FProfunctorDimap id f term))

instance Inject2 FProfunctor f => Profunctor (Fix f) where
    dimap l r term = Fix (inject2 (FProfunctorDimap l r term))

instance Inject2 FCategory f => Category (Fix f) where
    id = Fix (inject2 (FCategoryId :: FCategory (Fix f) t t))
    (.) x y = Fix (inject2 (FCategoryComp x y))

-- Need FProfunctor as well, to resolve the Functor superclass.
instance (Inject2 FProfunctor f, Inject2 FApplicative f) => Applicative (Fix f a) where
    pure (x :: t) = Fix (inject2 (FApplicativePure x :: FApplicative (Fix f) a t))
    (<*>) x y = Fix (inject2 (FApplicativeAp x y))

instance (Inject2 FProfunctor f, Inject2 FApplicative f, Inject2 FAlternative f) => Alternative (Fix f a) where
    empty = Fix (inject2 (FAlternativeEmpty :: FAlternative (Fix f) a t))
    (<|>) x y = Fix (inject2 (FAlternativePlus x y))

instance (Inject2 FCategory f, Inject2 FArrow f) => Arrow (Fix f) where
    arr (f :: s -> t) = Fix (inject2 (FArrow f :: FArrow (Fix f) s t))
    first term = Fix (inject2 (FFirst term))

instance (Inject2 FCategory f, Inject2 FArrow f, Inject2 FArrowChoice f) => ArrowChoice (Fix f) where
    left = Fix . inject2 . FLeft

instance (Inject2 FProfunctor f, Inject2 FApplicative f, Inject2 FMonad f) => Monad (Fix f a) where
    return (x :: t) = Fix (inject2 (FMonadReturn x :: FMonad (Fix f) a t))
    (>>=) x k = Fix (inject2 (FMonadBind x k))


-- TODO TBD move these classes, but to where?

-- Like a Kleisli arrow, but for an applicative.
class ApArrow (f :: * -> * -> *) where
    aaPure :: t -> f s t
    aaApply :: f s (t -> u) -> f s t -> f s u

instance Applicative f => ApArrow (Kleisli f) where
    aaPure x = Kleisli (\s -> pure x)
    aaApply left right = Kleisli (\s -> runKleisli left s <*> runKleisli right s)

class AltArrow (f :: * -> * -> *) where
    altEmpty :: f s t
    altPlus :: f s t -> f s t -> f s t

instance Alternative f => AltArrow (Kleisli f) where
    altEmpty = Kleisli (\_ -> empty)
    altPlus left right = Kleisli (\s -> runKleisli left s <|> runKleisli right s)

class KleisliArrow (m :: * -> * -> *) where
    kaReturn :: t -> m s t
    kaBind :: m s t -> (t -> m s u) -> m s u

instance Monad m => KleisliArrow (Kleisli m) where
    kaReturn x = Kleisli (\s -> return x)
    kaBind x k = Kleisli (\s -> runKleisli x s >>= ((flip runKleisli) s . k))
