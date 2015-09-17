Constructing Algebra
--------------------

Here we give an example use of the Control.Freedom.Construction module to
build a DSL for some algebraic structures.

As always, we begin with some noise.

> {-|
> Module      : Examples.Algebra
> Description : A DSL for some algebra.
> Copyright   : (c) Alexander Vieth, 2015
> Licence     : BSD3
> Maintainer  : aovieth@gmail.com
> Stability   : experimental
> Portability : non-portable (GHC only)
> -}
> 
> {-# LANGUAGE AutoDeriveTypeable #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE UnicodeSyntax #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE PartialTypeSignatures #-}
>
> module Examples.Algebra where
> 
> import Prelude hiding ((.), id, (+))
> import Control.Category
> import Control.Freedom.Construction

The goal is to obtain a datatype which is precisely the set of expressions in
the ring of multiplication over the additive group of integers. In other words:
plus, minus, and times. We shall build it from tiny parts, with the help of
`Control.Freedom.Construction`.

We start by coding in sums. We don't fix it to sums of numbers, but give the
type parameter `a` to control this. Here's the datatype:

> data Sum (a :: *) (left :: (* -> * -> *) -> * -> * -> *) (right :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
>     Sum :: left h s a -> right h s a -> Sum a left right h s a

It exhibits a kind of normal-form that I've observed in writing the `freedom`
library: it accepts 0 or more `(* -> * -> *) -> * -> * -> *` types and
terminates with `(* -> * -> *) -> * -> * -> *` (that's the `h`, `s`, and `t`
part). This schema allows us to feed normal-form datatypes (let's call them
freedom-normal-form datatypes) back into themselves, to obtain recursive
datatypes.

With `Sum` in hand, and `Pure`, `Rec` imported from
`Control.Freedom.Construction`, we can immediately describe the type of terms
in the additive semigroup of something (addition, but no negation).

> type FSemigroup a = Sum a Rec Rec + Pure
> type Semigroup a = Fix (FSemigroup a)

The type `FSemigroup` describes the form of the terms in the additive
semigroup: you're either a sum of two additive semigroup terms, or a pure
(Haskell) value. `Semigroup` uses the `Fix` type to bring
`FSemigroup` to life, plugging those `Rec` holes with
`FSemigroup` itself!

Some terms from `Semigroup` follow. They're not so pleasant to write.
Note the choice of `[()]` for values in the additive semigroup. It might be
confusing to choose `Int` or `Integer` instead, since these include additive
inverses, which might lead one to believe that `Semigroup Integer` is
in fact the additive group! That would be a mistake, though, because these are
formal sums; in `Semigroup`, `1 + -1` is irreducible.

> onePlusOne :: Semigroup [()] s [()]
> onePlusOne = inj (Sum (Rec (inj (Pure (const [()])))) (Rec (inj (Pure (const [()])))))
>
> onePlusOnePlusOne :: Semigroup [()] s [()]
> onePlusOnePlusOne = inj (Sum (Rec onePlusOne) (Rec (inj (Pure (const [()])))))
>
> somePlusOne :: Semigroup [()] [()] [()]
> somePlusOne = inj (Sum (Rec (inj (Pure id))) (Rec (inj (Pure (const [()])))))

Notice the use of `Pure id` in the last term, which yields `[()]` rather than
a free variable for the first parameter of `Semigroup`. Built-in to
this term is a dependency on some Haskell value: you've got to feed an `[()]`
in order to fill out the expression.

Moving on to products:

> data Product (a :: *) (left :: (* -> * -> *) -> * -> * -> *) (right :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
>     Product :: left h s a -> right h s a -> Product a left right h s a

This is exactly the same as `Sum`. We can use it, just like `Sum`, to get the
multiplicative semigroup of integers, but instead we'll throw it in *with*
`Sum` to obtain a semiring:

> type FSemiring a = Product a Rec Rec + FSemigroup a
> type Semiring a = Fix (FSemiring a)

The `Rec`s present in `FSemigroup a` are plugged with
`FSemiring a`, which means we have, in `Semiring`, products
of sums, products of products, products of pure values, *and* sums of
sums, sums of products, sums of pures. If we wanted a smaller type in which,
say, sums of products are ruled out, we would use the `Close` type:

> type FWeird a = Product a Rec Rec + Close (FSemigroup a)
> type Weird a = Fix (FWeird a)

`Close` cuts off its parameter from recursion via `Fix` by `Fix`ing its
parameter.

Terms of `Semiring [()]` are still rather painful to write, but this
demonstration wouldn't be complete without at least one example:

> twoTimesOnePlusOne :: Semiring [()] s [()]
> twoTimesOnePlusOne = inj (Product
>       (Rec (inj (Pure (const [()]))))
>       (Rec (inj (Sum (Rec (inj (Pure (const [()])))) (Rec (inj (Pure (const [()])))))))
>     )

Throwing in negation is trivial:

> data Negate (a :: *) (f :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
>     Negate :: f h s a -> Negate a f h s a
>
> type FRing a = Negate a Rec + FSemiring a
> type Ring a = Fix (FRing a)
>
> negativeTwoTimesOnePlusOne :: Ring [()] s [()]
> negativeTwoTimesOnePlusOne = inj (Negate
>         (Rec (inj (Product
>             (Rec (inj (Pure (const [()]))))
>             (Rec (inj (Sum (Rec (inj (Pure (const [()])))) (Rec (inj (Pure (const [()])))))))
>         )))
>     )

If we want to throw in multiplicative inverses to obtain a field, we do
precisely what was done for additive inverses, inventing a new datatype so
that we can distinguish the two inversions.

> data Invert (a :: *) (f :: (* -> * -> *) -> * -> * -> *) (h :: * -> * -> *) (s :: *) (t :: *) where
>     Invert :: f h s a -> Invert a f h s a
>
> type FField a = Invert a Rec + FRing a
> type Field a = Fix (FField a)
>
> oneHalf :: Field [()] s [()]
> oneHalf = inj (Invert
>         (Rec (inj (Pure (const [()]))))
>     )

To make term writing a little less painful, we'll define some infix functions
with the help of unicode syntax.

> lit = Pure . const
>
> infixr 1 +
> (+) x y = Sum x y
> 
> infixr 1 ×
> (×) x y = Product x y
> 
> infixr 1 −
> (−) x y = Sum x (Rec (inj (Negate y)))
>
> infixr 1 ÷
> (÷) x y = Product x (Rec (inj (Invert y)))
> 
> twoFifths :: Field [()] s [()]
> twoFifths = inj $
>       (Rec (inj ((Rec (inj (lit [()]))) + (Rec (inj (lit [()]))))))
>     ÷ (Rec (inj (lit [(), (), (), (), ()])))

Ok, it's not much better. The `Rec` and `inj` noise is almost unbearable.
