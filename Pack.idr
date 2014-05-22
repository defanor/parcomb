-- Perl-style pack/unpack

module Pack

-- core

-- inp - a parsing-oriented type, i.e. including bits count or similar
-- information; it's constructors should accept a final argument of
-- type out
-- out - a user-friendly type, e.g. Nat or String
class Packable inp out where
  total ppack : inp -> Maybe (List Bool)
  total punpack : List Bool -> Maybe (out, List Bool)

-- collecting all the types, user should only provide functions of
-- type (out -> inp), e.g. (mkpNat 3)
data Pack : Type -> Type -> Type where
  p : Packable i o => (o -> i) -> Pack i o
  (..) : Packable i o => (o -> i) -> Pack a b -> Pack (i, a) (o, b)
  
infixr 3 ..

-- actual pack
total mpack : Pack t1 t2 -> t2 -> Maybe (List Bool)
mpack (p tc) o = ppack (tc o)
mpack (tc .. pl) (v, vl) = do
  this <- ppack (tc v)
  rest <- mpack pl vl
  return $ this ++ rest

-- and unpack

total munpack : Pack t1 t2 -> List Bool -> Maybe t2
munpack (p tc) l = (punpack l) >>= Just . fst
munpack (tc .. pl) l = do
  (r, rest) <- punpack l
  next <- munpack pl rest
  return (r, next)



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
    (mkpNat n v) => if S (log2 v) <= n
                    then Just $ natToBits v n
                    else Nothing
  punpack l = if n <= length l
              then Just (bitsToNat (take n l) n, drop n l)
              else Nothing

-- Nat, LE

data pNatLe : Nat -> Type where
  mkpNatLe : (bits : Nat) -> Nat -> pNatLe bits

instance Packable (pNatLe n) Nat where
  ppack mn = case mn of
    (mkpNatLe n v) => if S (log2 v) <= n
                      then Just $ reverse $ natToBits v n
                      else Nothing
  punpack l = if n <= length l
              then Just (bitsToNat (reverse $ take n l) n, drop n l)
              else Nothing

-- Raw bits

data pBits : Nat -> Type where
  mkpBits : (bits : Nat) -> List Bool -> pBits bits

instance Packable (pBits n) (List Bool) where
  ppack bl = case bl of
    (mkpBits n l) => if length l == n
                     then Just $ l
                     else Nothing
  punpack l = if n <= length l
              then Just (take n l, drop n l)
              else Nothing



-- Verified Packable

data T = tt

class Packable i o => VerifiedPackable i o (f : o -> i) where
  total v1 : (outv : o) -> maybe T (\x => x = (outv, List.Nil {a=Bool})) (ppack (f outv) >>= punpack {inp=i} {out=o})


-- should be useful if i'll be able to pass ((length xs == m) = True)
total nat_eqb_eq : (x : Nat) -> (y : Nat) -> (x == y = True) -> (x = y)
nat_eqb_eq Z Z p = refl
nat_eqb_eq Z (S y) p = FalseElim (trueNotFalse (sym p))
nat_eqb_eq (S x) Z p = FalseElim (trueNotFalse (sym p))
nat_eqb_eq (S x) (S y) p = cong {f=S} (nat_eqb_eq x y p)

vp_pbits_lemma2 : (xs : List Bool) -> (m : Nat) -> (n : Nat) -> maybe T (\x2 => x2 = (x :: xs, List.Nil {a=Bool}))
  (if (n <= (S (length xs))) then (Just (take n (x :: xs), drop n (x :: xs))) else Nothing)
vp_pbits_lemma2 xs m n with (n <= (S (length xs)))
  | True = ?c0 -- need to get (length xs == m) here, but it's lost on "with"
  | False = tt

vp_pbits_lemma : (xs : List Bool) -> (m : Nat) -> maybe T (\x2 => x2 = (x :: xs, List.Nil {a=Bool}))
  ((if (length xs == m) then ((Just (x :: xs))) else Nothing) >>= punpack {inp=pBits n} {out=List Bool})
vp_pbits_lemma xs m with (length xs == m)
  | False = tt
  | True = ?c1           

instance VerifiedPackable (pBits n) (List Bool) (mkpBits n) where
  v1 [] = case n of
    Z => refl
    (S m) => tt
  v1 (x :: xs) = case n of
    Z => tt
    (S m) => ?c2
