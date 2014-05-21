-- Perl-style pack/unpack

-- let expr = ((mkpNat 3) .. (mkpNatLe 7) .. (mkpBits 3) .. (p $ mkpNat 5)) in munpack expr $ mpack expr (1,13,[True, False, True], 23)
-- (1, 13, [True, False, True], 23) : (Nat, Nat, List Bool, Nat)

module Pack

-- core

-- inp - a parsing-oriented type, i.e. including bits count or similar
-- information; it's constructors should accept a final argument of
-- type out
-- out - a user-friendly type, e.g. Nat or String
class Packable inp out where
  total ppack : inp -> List Bool
  total punpack : List Bool -> (out, List Bool)

-- collecting all the types, user should only provide functions of
-- type (out -> inp), e.g. (mkpNat 3)
data Pack : (Type, Type) -> Type where
  p : Packable i o => (o -> i) -> Pack (i, o)
  (..) : Packable i o => (o -> i) -> Pack (a, b) -> Pack ((i, a), (o, b))

infixr 3 ..

-- actual pack
total mpack : Pack (t1, t2) -> t2 -> List Bool
mpack (p tc) o = ppack (tc o)
mpack (tc .. pl) (v, vl) = ppack (tc v) ++ mpack pl vl

-- and unpack
total munpack : Pack (t1, t2) -> List Bool -> t2
munpack (p tc) l = fst (punpack l)
munpack (tc .. pl) l = let (r, rest) = (punpack l) in (r, munpack pl rest)

-- extensions

natToBits : Nat -> Nat -> List Bool
natToBits n Z = []
natToBits Z bits = replicate bits False
natToBits n (S bits) = natToBits (div n 2) bits ++ [ (mod n 2 /= Z) ]

bitsToNat : List Bool -> Nat -> Nat
bitsToNat l b = bitsToNat' (reverse l) b
  where bitsToNat' [] b = Z
        bitsToNat' l Z = Z
        bitsToNat' (v :: l) (S b) = (if v then 1 else 0) + 2 * bitsToNat' l b

-- Nat, BE

data pNat : Nat -> Type where
  mkpNat : (bits : Nat) -> Nat -> pNat bits

instance Packable (pNat n) Nat where
  ppack mn = case mn of
    (mkpNat n v) => natToBits v n
  punpack l = (bitsToNat (take n l) n, drop n l)

-- Nat, LE

data pNatLe : Nat -> Type where
  mkpNatLe : (bits : Nat) -> Nat -> pNatLe bits

instance Packable (pNatLe n) Nat where
  ppack mn = case mn of
    (mkpNatLe n v) => reverse $ natToBits v n
  punpack l = (bitsToNat (reverse $ take n l) n, drop n l)

-- Raw bits

data pBits : Nat -> Type where
  mkpBits : (bits : Nat) -> List Bool -> pBits bits

instance Packable (pBits n) (List Bool) where
  ppack bl = case bl of
    (mkpBits n l) => replicate (n - length l) False ++ l
  punpack l = (take n l, drop n l)

-- Nat, unary

data pNatUnary : Type where
  mkpNatUnary : Nat -> pNatUnary

instance Packable pNatUnary Nat where
  ppack (mkpNatUnary n) = replicate n True ++ [False]
  punpack l = (n, drop (S n) l)
    where n = length (takeWhile (== True) l)



-- VerifiedPackable: commented out for now, simple Packable should be
-- refined first

-- class Packable i o => VerifiedPackable i o (f : o -> i) where
--   v1 : (outv : o) -> fst (punpack {inp=i} {out=o} (ppack (f outv))) = outv

-- data vPack : (Type, Type) -> Type where
--   vp : VerifiedPackable i o f => (o -> i) -> (o -> i) = f -> vPack (i, o)
--   (...) : VerifiedPackable i o f => (o -> i) -> (o -> i) = f -> vPack (a, b) -> vPack ((i, a), (o, b))

-- instance VerifiedPackable pNatUnary Nat mkpNatUnary where
--   v1 Z = refl
--   v1 (S k) = cong {f=S} ?v1k
