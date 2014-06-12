# ISD with some verification #

An Idris implementation of
[Invertible syntax descriptions](http://www.informatik.uni-marburg.de/~rendel/unparse/),
with verified partial isomorphisms:

    data PartIso : Type -> Type -> Type where
      MkPartIso : (to : a -> Maybe b) ->
                  (from : b -> Maybe a) ->
                  (toFrom : (y : b) -> maybe () (\x => to x = Just y) (from y)) ->
                  (fromTo : (x : a) -> maybe () (\y => from y = Just x) (to x)) ->
                  PartIso a b

Targeting binary file formats and network protocols.


## Example ##

    test4 : Syntax d Bool => d (Vect 2 Nat, Bool) Bool
    test4 = rep 2 (nat LE 4) <*> val True
        <|> rep 2 (nat BE 3) <*> val False


    λΠ> compose test4 ([1,2], True)
    Just [True, False, False, False, False, True, False, False, True] : Maybe (List Bool)

    λΠ> compose test4 ([1,2], False)
    Just [False, False, True, False, True, False, False] : Maybe (List Bool)

    λΠ> parse test4 [True, False, False, False, False, True, False, False, True]
    Just ([1, 2], True) : Maybe (Vect 2 Nat, Bool)

    λΠ> parse test4 [False, False, True, False, True, False, False]
    Just ([1, 2], False) : Maybe (Vect 2 Nat, Bool)


## TODO ##

Probably will add more parsers, and it also would be nice to verify
parse/compose functions somehow.
