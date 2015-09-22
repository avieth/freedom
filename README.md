freedom
-------

Why bother? This style of programming lifts the *shape* of our datatypes into
the type level. The difference between

```Haskell
data Maybe t = Just t | Nothing
```

and

```Haskell
type Maybe = Pure + None
```

seems superficial, but the crucial difference is that we cannot get a hold of
`|` at the type level, whereas `+` is a type like any other, and so we are
able to use it in type-level programs. With this library, the `|` is used *once*
(in the definition of `+`), and need never be used again.

New datatypes are expressed as singleton (G)ADTs in a normal form: they
have kind

```Haskell
k -> l -> (* -> * -> *) -> * -> * -> *
```

where `l` is 0 or more occurrences of a `(* -> * -> *) -> * -> * -> *` kind.

The intended use case for this library is the construction of (E)DSLs.
Suppose we had a little DSL for sound processing:

```Haskell
data MyDSL where
    Amplify :: MyDSL -> MyDSL
    LowPassFilter :: Frequency -> MyDSL -> MyDSL
    Source :: SourceID -> MyDSL
```

We would write this in freedom-style like so:

```Haskell
type FMyDSL = Amplify Rec + Filter Pure Rec + Source
type MyDSL = Fix FMyDSL

data Source h s t where
    Source :: h () SourceID -> Source h () ()

data Amplify f h s t where
    Amplify :: f h () () -> Amplify f h () ()

data Filter f g h s t where
    Filter :: f h () Frequency -> g h () () -> Filter f g h () ()
```

Recursive datatype are obtained by using the `Rec` type, which in this case is
substituted for `f` in `Amplify` and `g` in `Filter`, to indicate that whatever
type is chosen for `h` shall be used in its place. The constructor `Fix` pipes
`FMyDSL` into its `h` parameter, bringing those `Rec` types to life.

Whenever a typical Haskell value is needed, the `Pure` type is chosen, as is
the case for `f` in `Filter`. Every GADT for use in this library is given
input and output types `s` and `t`. Since this example DSL is a purely
*symbolic* one--meaning its terms do not contain any Haskell functions--the
input and output types are always `()`.

To compute with freedom-normal-form datatypes, we simulate `case` pattern
matching by giving a function for each summand, all with common codomain.

```Haskell
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
```
