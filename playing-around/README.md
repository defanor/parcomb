parcomb
=======

Playing with parsing in Idris.

The ultimate goal is to get handy and verified (easily verifiable)
parser/printer combinators (allowing to use a single structure
definition for both directions), suitable for parsing of both binary
and textual network protocols and file formats.


## Parcomb ##

Toy parser combinators.


## Pack ##

Binary (`List Bool` for now, actually) pack/unpack, inspired by those
of Perl. Uses the same structure definition for both directions.


## Invertible ##

An attempt to rewrite
[Invertible syntax descriptions](http://www.informatik.uni-marburg.de/~rendel/unparse/)
in Idris, and to try to make it usable afterwards.

The following changes were made:

1. `String` was replaced with `List γ` in order to make it more general
2. `many` is implemented with an upper bound argument, which is not
   that nice


## InvParComb ##

A messy mix of the above.


## InvParComb2 ##

A fork of Invertible: cleaner, with necessary laziness and nicer
`many`, and using Maybe instead of List.


## VerifiedInvertible ##

InvParComb2 with verified partial isomorphisms, except for `ignore`:

    data PartIso : Type -> Type -> Type where
      MkPartIso : (to : a -> Maybe b) ->
                  (from : b -> Maybe a) ->
                  (toFrom : (y : b) -> maybe T (\x => x = y) (from y >>= to)) ->
                  (fromTo : (x : a) -> maybe T (\y => y = x) (to x >>= from)) ->
                  PartIso a b

`toFrom` and `fromTo` may be stronger here: for now they just say that
there could not be wrong results, if those results are not errors, but
there's no warranty that it'll be able to parse whatever it composed
and vice versa.


## VerifiedInvertible2 ##

VerifiedInvertible, but with more strict properties:

    data PartIso : Type -> Type -> Type where
      MkPartIso : (to : a -> Maybe b) ->
                  (from : b -> Maybe a) ->
                  (toFrom : (y : b) -> maybe T (\x => to x = Just y) (from y)) ->
                  (fromTo : (x : a) -> maybe T (\y => from y = Just x) (to x)) ->
                  PartIso a b

It's probably the final version of this "playing around".
