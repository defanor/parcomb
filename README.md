parcomb
=======

Playing with parsing in Idris.


## Parcomb ##

Toy parser combinators.


## Pack ##

Binary (`List Bool` for now, actually) pack/unpack, inspired by those
of Perl. Uses the same structure definition for both directions.

### Examples ###

    λΠ> let expr = ((mkpNat 2) .. (mkpBits 3) .. (mkpNatLe 5) .. (p $ mkpNat 8)) in mpack expr (15, [True, False, True], 22, 42)
    Nothing : Maybe (List Bool)
    
    λΠ> let expr = ((mkpNat 2) .. (mkpBits 3) .. (mkpNatLe 5) .. (p $ mkpNat 8)) in mpack expr (2, [True, False, True], 22, 42)
    Just [True, False, True, False, True, False, True, True, False, True, False, False, True, False, True, False, True, False] : Maybe (List Bool)

    λΠ> let expr = ((mkpNat 2) .. (mkpBits 3) .. (mkpNatLe 5) .. (p $ mkpNat 8)) in mpack expr (2, [True, False, True], 22, 42) >>= munpack expr
    Just (2, [True, False, True], 22, 42) : Maybe (Nat, List Bool, Nat, Nat)
    
    λΠ> let expr = ((mkpNat 2) .. (mkpBits 3) .. (mkpNatLe 5) .. (p $ mkpNat 8)) in munpack expr [True, False, True, False, True, False, True, True, False, True, False, False, True, False, True, False, True, False]
    Just (2, [True, False, True], 22, 42) : Maybe (Nat, List Bool, Nat, Nat)
    
    λΠ> let expr = ((mkpNat 2) .. (mkpBits 3) .. (mkpNatLe 5) .. (p $ mkpNat 8)) in munpack expr [True, False, True, False, True, False, True, True, False, True, False, False, True, False, True, False, True]
    Nothing : Maybe (Nat, List Bool, Nat, Nat)
