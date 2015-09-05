{-|
Module      : Control.Freedom.Interpretation
Description : Interpretation of free structures.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)

Description of the interpretation of free structures. This is accomplished
by providing injections of each summand into a common target.

-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}

module Control.Freedom.Interpretation (

      type (%)
    , (%)
    , type (~>)
    , I
    , IFix
    , Interpreter(..)
    , runInterpreter
    , Interprets
    , interpret
    , runFix
    , profunctorInterpreter
    , categoryInterpreter
    , applicativeInterpreter
    , alternativeInterpreter
    , arrowInterpreter
    , arrowChoiceInterpreter
    , monadInterpreter

    ) where

import Prelude hiding (id, (.))
import Control.Freedom.Construction
import Control.Category
import Control.Arrow
import Data.Profunctor

infixr 8 %
type int1 % int2 = (int1, int2)

(%) = (,)

type family I (ts :: (* -> * -> *) -> * -> * -> *) (g :: * -> * -> *) where
    I ts g = IFix (Fix ts) ts g

type family IFix (fix :: * -> * -> *) (is :: (* -> * -> *) -> * -> * -> *) (g :: * -> * -> *) where
    IFix fix (f1 + f2) g = (Interpreter fix f1 g, IFix fix f2 g)
    IFix fix f1 g = Interpreter fix f1 g

infixl 1 ~>
type ts ~> g = I ts g

data Interpreter (h :: * -> * -> *) (f :: (* -> * -> *) -> * -> * -> *) (g :: * -> * -> *)  where
    Interpreter :: (forall s t . (forall s t . h s t -> g s t) -> f h s t -> g s t) -> Interpreter h f g

runInterpreter :: Interpreter h f g -> (forall s t . (forall s t . h s t -> g s t) -> f h s t -> g s t)
runInterpreter term = case term of
    Interpreter f -> f

class Interprets i h f g where
    interpret :: i -> (forall s t . (forall s t . h s t -> g s t) -> f h s t -> g s t)

instance Interprets (Interpreter h f g) h f g where
    interpret = runInterpreter

instance
    ( Interprets i h f1 g
    , Interprets j h f2 g
    ) => Interprets (i % j) h (f1 + f2) g
  where
    interpret (left, right) = \recurse sumTerm -> case sumTerm of
        F2SumLeft term -> interpret left recurse term
        F2SumRight term -> interpret right recurse term

runFix :: Interprets i (Fix f) f g => i -> Fix f s t -> g s t
runFix i fixTerm = case fixTerm of
    Fix term -> interpret i (runFix i) term

profunctorInterpreter :: Profunctor g => Interpreter h FProfunctor g
profunctorInterpreter = Interpreter $ \recurse term -> case term of
    FProfunctorDimap l r term -> dimap l r (recurse term)

categoryInterpreter :: Category g => Interpreter h FCategory g
categoryInterpreter = Interpreter $ \recurse term -> case term of
    FCategoryId -> id
    FCategoryComp left right -> recurse left . recurse right

applicativeInterpreter :: ApArrow g => Interpreter h FApplicative g
applicativeInterpreter = Interpreter $ \recurse term -> case term of
    FApplicativePure x -> aaPure x
    FApplicativeAp f x -> recurse f `aaApply` recurse x

alternativeInterpreter :: AltArrow g => Interpreter h FAlternative g
alternativeInterpreter = Interpreter $ \recurse term -> case term of
    FAlternativeEmpty -> altEmpty
    FAlternativePlus left right -> recurse left `altPlus` recurse right

arrowInterpreter :: Arrow g => Interpreter h FArrow g
arrowInterpreter = Interpreter $ \recurse term -> case term of
    FArrow f -> arr f
    FFirst term -> first (recurse term)

arrowChoiceInterpreter :: ArrowChoice g => Interpreter h FArrowChoice g
arrowChoiceInterpreter = Interpreter $ \recurse term -> case term of
    FLeft term -> left (recurse term)

monadInterpreter :: KleisliArrow g => Interpreter h FMonad g
monadInterpreter = Interpreter $ \recurse term -> case term of
    FMonadReturn x -> kaReturn x
    FMonadBind x k -> recurse x `kaBind` (recurse . k)

{-
data Ex1 f s t where
    Add :: Ex1 f (Int, Int) Int

data Ex2 u f s t where
    Log :: Ex2 u f u ()

type Ex = Fix (FArrow + FCategory + Ex1 + Ex2 String)

exTerm :: Ex (Int, Int) Int
exTerm = proc (x, y) -> do
    sum <- inj Add -< (x, y)
    () <- inj Log -< show sum
    returnA -< sum

ex1Interpreter :: Interpreter h Ex1 (Kleisli IO)
ex1Interpreter = Interpreter $ \_ term -> case term of
    Add -> Kleisli $ \(x, y) -> return (x + y)

ex2Interpreter :: Show u => Interpreter h (Ex2 u) (Kleisli IO)
ex2Interpreter = Interpreter $ \_ term -> case term of
    Log -> Kleisli $ \s -> print s

{-
exInterpreter
    :: Interpreter Ex FArrow (Kleisli IO)
    %  Interpreter Ex FCategory (Kleisli IO)
    %  Interpreter Ex Ex1 (Kleisli IO)
    %  Interpreter Ex (Ex2 String) (Kleisli IO)
-}
exInterpreter :: (FArrow + FCategory + Ex1 + Ex2 String) ~> (Kleisli IO)
exInterpreter =
      arrowInterpreter
    % categoryInterpreter
    % ex1Interpreter
    % ex2Interpreter
-}

{-
data Interpreter (f :: * -> * -> *) (g :: * -> * -> *)  where
    Interpreter :: (forall s t . f s t -> g s t) -> Interpreter f g

runInterpreter :: Interpreter f g -> (forall s t . f s t -> g s t)
runInterpreter term = case term of
    Interpreter f -> f

class Interprets i f g where
    interpret :: i -> (forall s t . f s t -> g s t)

instance Interprets (Interpreter f g) f g where
    interpret = runInterpreter

instance
    ( Interprets i (f1 h) g
    , Interprets j (f2 h) g
    ) => Interprets (i % j) ((f1 + f2) h) g
  where
    interpret (left, right) = \sumTerm -> case sumTerm of
        F2SumLeft term -> interpret left term
        F2SumRight term -> interpret right term

instance
    ( Interprets i (f (Fix f)) g
    ) => Interprets i (Fix f) g
  where
    interpret i = \fixTerm -> case fixTerm of
        Fix term -> interpret i term

categoryInterpreter :: Category g => (forall s t . h s t -> g s t) -> Interpreter (FCategory h) g
categoryInterpreter recurse = Interpreter $ \term -> case term of
    FCategoryId -> id
    FCategoryComp left right -> recurse left . recurse right

arrowInterpreter :: Arrow g => (forall s t . h s t -> g s t) -> Interpreter (FArrow h) g
arrowInterpreter recurse = Interpreter $ \term -> case term of
    FArrow f -> arr f
    FFirst term -> first (recurse term)

data Ex1 f s t where
    Add :: Ex1 f (Int, Int) Int

data Ex2 u f s t where
    Log :: Ex2 u f u ()

type Ex = Fix (FArrow + FCategory + Ex1 + Ex2 String)

exTerm :: Ex (Int, Int) Int
exTerm = proc (x, y) -> do
    sum <- inj Add -< (x, y)
    () <- inj Log -< show sum
    returnA -< sum

ex1Interpreter :: Interpreter (Ex1 h) (Kleisli IO)
ex1Interpreter = Interpreter $ \term -> case term of
    Add -> Kleisli $ \(x, y) -> return (x + y)

ex2Interpreter :: Show u => Interpreter (Ex2 u h) (Kleisli IO)
ex2Interpreter = Interpreter $ \term -> case term of
    Log -> Kleisli $ \s -> print s

exInterpreter
    :: Interpreter (FArrow Ex) (Kleisli IO)
    %  Interpreter (FCategory Ex) (Kleisli IO)
    %  Interpreter (Ex1 Ex) (Kleisli IO)
    %  Interpreter (Ex2 String Ex) (Kleisli IO)
exInterpreter =
      arrowInterpreter (interpret exInterpreter)
    % categoryInterpreter (interpret exInterpreter)
    % ex1Interpreter
    % ex2Interpreter
-}
