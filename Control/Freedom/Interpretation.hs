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
{-# LANGUAGE ScopedTypeVariables #-}

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
    , interpretFix

    , recInterpreter
    , closeInterpreter
    , pureInterpreter
    , noneInterpreter
    , dimapInterpreter
    , dotInterpreter
    , sequenceInterpreter
    , applyInterpreter
    , joinInterpreter

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
        FSumL term -> interpret left recurse term
        FSumR term -> interpret right recurse term

interpretFix :: Interprets i (Fix f) f g => i -> Fix f s t -> g s t
interpretFix i fixTerm = case fixTerm of
    Fix term -> interpret i (interpretFix i) term

recInterpreter :: Interpreter h Rec g
recInterpreter = Interpreter $ \recurse term -> case term of
    Rec subterm -> recurse subterm

closeInterpreter :: Interpreter (Fix f) (Close f) g
closeInterpreter = Interpreter $ \recurse term -> case term of
    Close fixTerm -> recurse fixTerm

pureInterpreter :: Interpreter h Pure (->)
pureInterpreter = Interpreter $ \recurse term -> case term of
    Pure f -> f

noneInterpreter :: g () () -> Interpreter h None g
noneInterpreter value = Interpreter $ \recurse term -> case term of
    None -> value

dimapInterpreter :: Profunctor g => Interpreter h f g -> Interpreter h (Dimap f) g
dimapInterpreter finterpreter = Interpreter $ \recurse term -> case term of
    Dimap l r term -> dimap l r ((runInterpreter finterpreter) recurse term)

dotInterpreter
    :: (Category g)
    => Interpreter h left g
    -> Interpreter h right g
    -> Interpreter h (Dot left right) g
dotInterpreter leftInterpreter rightInterpreter = Interpreter $ \recurse term -> case term of
    Dot left right -> (runInterpreter leftInterpreter recurse left) . (runInterpreter rightInterpreter recurse right)

sequenceInterpreter
    :: ( forall s t . g s () -> g s t -> g s t )
    -> Interpreter h left g
    -> Interpreter h right g
    -> Interpreter h (Sequence left right) g
sequenceInterpreter next leftInterpreter rightInterpreter = Interpreter $ \recurse term -> case term of
    Sequence left right -> (runInterpreter leftInterpreter recurse left) `next` (runInterpreter rightInterpreter recurse right)

applyInterpreter
    :: ( )
    => (forall s t u . g s (t -> u) -> g s t -> g s u )
    -> Interpreter h f1 g
    -> Interpreter h f2 g
    -> Interpreter h (Apply f1 f2) g
applyInterpreter apply f1interpreter f2interpreter = Interpreter $ \recurse term -> case term of
    Apply f1 f2 -> (runInterpreter f1interpreter recurse f1) `apply` (runInterpreter f2interpreter recurse f2)

{-
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
-}

joinInterpreter 
    :: ( )
    => (forall s t u . (t -> u) -> g s t -> g s u)
    -> (forall s t u . (g s (g s u)) -> g s u)
    -> Interpreter h f1 g
    -> Interpreter h f2 g
    -> Interpreter h (Join f1 f2) g
joinInterpreter fmap join f1interpreter f2interpreter = Interpreter $ \recurse term -> case term of
    Join term -> join (fmap (runInterpreter f2interpreter recurse) (runInterpreter f1interpreter recurse term))
