parcomb
=======

Playing with parsing in Idris.


## Parcomb ##

Toy parser combinators.


## Pack ##

Binary (`List Bool` for now, actually) pack/unpack, inspired by those
of Perl. Uses the same structure definition for both directions.

Examples:

    λΠ> let expr = ((mkpNat 3) .. (mkpNatLe 7) .. (mkpBits 3) .. (p $ mkpNat 5)) in mpack expr (1,13,[True, False, True], 23)
    [False, False, True, True, False, True, True, False, False, False, True, False, True, True, False, True, True, True] : List Bool

    λΠ> let expr = ((mkpNat 3) .. (mkpNatLe 7) .. (mkpBits 3) .. (p $ mkpNat 5)) in munpack expr $ mpack expr (1,13,[True, False, True], 23)
    (1, 13, [True, False, True], 23) : (Nat, Nat, List Bool, Nat)

    λΠ> let expr = ((mkpNat 3) .. (mkpNatLe 7) .. (mkpBits 3) .. (p $ mkpNat 5)) in munpack expr [False, False, True, True, False, True, True, False, False, False, True, False, True, True, False, True, True, True]
    (1, 13, [True, False, True], 23) : (Nat, Nat, List Bool, Nat)
