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

import Prelude hiding ((.), id)
import GHC.TypeLits hiding (type (+))
import Control.Category
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
    FSumIndicator (g + h) = FSumMultiple
    FSumIndicator g = FSumSingle

class Inject2' (indicator :: FSumType) (f :: (* -> * -> *) -> * -> * -> *) (g :: (* -> * -> *) -> * -> * -> *) where
    inject2' :: Proxy indicator -> f hs a b -> g hs a b

instance Inject2Single f g => Inject2' FSumSingle f g where
    inject2' _ = inject2Single

instance Inject2Multiple f g => Inject2' FSumMultiple f g where
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

-- We represent values as Pure.
data Pure (h :: * -> * -> *) (s :: *) (t :: *) where
    Pure :: ((->) s t) -> Pure h s t

-- We represent recursion as Rec (example below).
data Rec (h :: * -> * -> *) (s :: *) (t :: *) where
    Rec :: h s t -> Rec h s t

-- Constructors with formal parameters must give the types of these parameters
-- in their own type.
data Sum (left :: (* -> * -> *) -> * -> * -> *) (right :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    Sum :: left h s Int -> right h s Int -> Sum left right h s Int

data Product (left :: (* -> * -> *) -> * -> * -> *) (right :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    Product :: left h s Int -> right h s Int -> Product left right h s Int

type Ex1 = Sum Rec Rec + Pure

ex1p1 :: Fix Ex1 () Int
ex1p1 = inj (Pure (const 1))

ex1p2 :: Fix Ex1 () Int
ex1p2 = inj (Sum (Rec (inj (Pure (const 1)))) (Rec (inj (Pure (const 2)))))

type Ex2 = Product (Sum Rec Rec) (Sum Rec Rec) + Pure

ex2p1 :: Fix Ex2 () Int
ex2p1 = inj (Product (Sum (Rec (inj (Pure (const 2)))) (Rec (inj (Pure (const 2))))) (Sum (Rec (inj (Pure (const 4)))) (Rec (inj (Pure (const 4))))))

data Negate (f :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    Negate :: f h s Int -> Negate f h s Int

-- Here's a familiar definition: 
--   data Ex3 = Product Ex3 Ex3 | Sum Ex3 Ex3 | Negate Ex3 | Pure Int
-- Notice how the Int mysteriously is not present in our definition.
-- Very curious.
type Ex3 = Product Rec Rec + Sum Rec Rec + Negate Rec + Pure

-- Now, suppose Ex3 is a very useful tool for us, but a new requirement comes
-- about and we need another DSL which contains Ex3, but also has provisions for
-- boolean-valued tests on integers.

data IsEven (f :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    IsEven :: f h s Int -> IsEven f h s Bool

data IfElse (test :: (* -> * -> *) -> * -> * -> *) (true :: (* -> * -> *) -> * -> * -> *) (false :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    IfElse :: test h s Bool -> true h s t -> false h s t -> IfElse test true false h s t

type Ex4 = IfElse Rec Rec Rec + IsEven Rec + Ex3

ex4p1 :: Fix Ex4 () Bool
ex4p1 = inj $ IfElse (Rec condition) (Rec true) (Rec false)
  where
    condition = inj $ IsEven (Rec (inj (Pure (const 1))))
    true = inj $ Pure (const False)
    false = inj $ Pure (const True)

-- Here's a cool one:

data Assign q r (left :: (* -> * -> *) -> * -> * -> *) (right :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    Assign :: left h s q -> right h s r -> Assign q r left right h s ()

data Inspect q r (left :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    Inspect :: left h s q -> Inspect q r left h s r

-- Here we say that we can
--   - Assign an Int to a Pure String, where the Int comes from any Rec.
--   - Inspect a Pure String to obtain an Int.
type Ex5 = Assign String Int Pure Rec + Inspect String Int Pure + Ex4

-- Here we write what might be recognized as
--   x := 2 + 2
ex5p1 :: Fix Ex5 () ()
ex5p1 = inj $ Assign (Pure (const "x")) (Rec computation)
  where
    computation = inj $ Sum (Rec (inj (Pure (const 2)))) (Rec (inj (Pure (const 2))))

-- But wait! Assignment and inspection aren't very useful without the ability
-- to sequence terms. Let's throw that in.
-- NB unlike the monad, applicative, etc. terms, this one can be applied without
-- making the thing an EDSL (it remains symbolic).

data Sequence (left :: (* -> * -> *) -> * -> * -> *) (right :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
    Sequence :: left h t u -> right h s t -> Sequence left right h s u

-- Note how to sequence backwards, to stay consistent with (.)
-- If we use unicode syntax, to workaround GHC's disdain for the ASCII
-- semicolon, then we can sequence using a semicolon-like thing, known as
-- the full-width semicolon (U+FF1B).
infixr 1 ；
(；) x y = Sequence y x

-- While we're at it, why not an assignment operator?
-- That's unicode 2254.
infixr 1 ≔
(≔) x y = Assign x y

infixr 1 ＋
(＋) x y = Sum (Rec (inj x)) (Rec (inj y))

infixr 1 －
(－) x y = Sum (Rec (inj x)) (Rec (inj (Negate (Rec (inj y)))))

-- Turns out this is half of the Category interface.
-- Here's the rest :)

data NoOp (h :: * -> * -> *) (s :: *) (t :: *) where
    NoOp :: NoOp h s s

-- A note on types for sequence: if we use it to describe a language like C,
-- then we can't sequence, for instance, a sum and a negate, but that's ok!
-- In C, you only sequence statements, whose output type is () because they
-- don't produce values! So we can sequence assignments, loops, function
-- definitions, etc., but not values.

type Ex6 = Sequence Rec Rec + Ex5

-- Something like
--
--     x := 1 + y
--     x - y
--
ex6p1 :: Fix Ex6 () Int
ex6p1 = inj $ (Rec (inj (x ≔ (Rec onePlusY)))) ； (Rec read)
  where

    onePlusY :: Fix Ex6 () Int
    onePlusY = inj $ Sum (Rec one) (Rec (inj (Inspect y)))

    one :: Fix Ex6 () Int
    one = inj $ (Pure (const (1 :: Int)))

    x :: Pure h () String
    x = Pure (const "x")

    y :: Pure h () String
    y = Pure (const "y")

    read = inj $ Sum (Rec (inj (Inspect (Pure (const "x"))))) (Rec (inj (Negate (Rec (inj (Inspect (Pure (const "y"))))))))

ex6p2 :: Fix Ex6 () Int
ex6p2 = inj (

      Rec (inj (x ≔ (Rec (inj ((lit 1) ＋ y'))))) ； 
      Rec (inj (x' －y'))

    )

  where

    lit :: Int -> Pure h () Int
    lit = Pure . const

    x :: Pure h () String
    x = Pure (const "x")

    x' :: Inspect String Int Pure h () Int
    x' = Inspect x

    y :: Pure h () String
    y = Pure (const "y")

    y' :: Inspect String Int Pure h () Int
    y' = Inspect y


-- Now for some more aspects:

data Dimap (h :: * -> * -> *) (s :: *) (t :: *) where
    Dimap :: (s -> s') -> (t' -> t) -> h s' t' -> Dimap h s t

data First (h :: * -> * -> *) (s :: *) (t :: *) where
    First :: h s t -> First h (s, c) (t, c)

data Apply (h :: * -> * -> *) (s :: *) (t :: *) where
    Apply :: h s (t -> u) -> h s t -> Apply h s u

--data Bind (h :: * -> * -> *) (s :: *) (t :: *) where
--    Bind :: h s t -> (t -> h s u) -> Bind h s u

data Join (h :: * -> * -> *) (s :: *) (t :: *) where
    Join :: h s (h s t) -> Join h s t

instance
    ( Inject2 Dimap f
    ) => Profunctor (Fix f)
  where
    dimap l r term = inj (Dimap l r term)

instance
    ( Inject2 Dimap f
    ) => Functor (Fix f s)
  where
    fmap = rmap

instance
    ( Inject2 Pure f
    , Inject2 (Sequence f f) f
    ) => Category (Fix f)
  where
    id = inj (Pure id)
    -- TBD why do we have to runFix here, but not in Profunctor, Applicative,
    -- nor Monad?
    -- Maybe something has gone wrong?
    -- Perhaps it's because Sequence, unlike Join or Apply etc. actually
    -- allows for its sub-terms to not be the recursive parameter.
    (.) left right = inj (Sequence (runFix left) (runFix right))

instance
    ( Inject2 Pure f
    , Inject2 Dimap f
    , Inject2 Apply f
    ) => Applicative (Fix f s)
  where
    pure = inj . Pure . const
    (<*>) left right = inj (Apply left right)

instance
    ( Inject2 Pure f
    , Inject2 (Sequence f f) f
    , Inject2 First f
    ) => Arrow (Fix f)
  where
    arr = inj . Pure
    first = inj . First

instance
    ( Inject2 Pure f
    , Inject2 Dimap f
    , Inject2 Apply f
    , Inject2 Join f
    ) => Monad (Fix f s)
  where
    return = pure
    (>>=) x k = inj (Join (fmap k x))


