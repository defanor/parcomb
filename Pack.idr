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

-- Verified Packable
data T = tt
class Packable i o => VerifiedPackable i o (f : o -> i) where
  total v1 : (outv : o) -> maybe T (\x => x = (outv, List.Nil {a=Bool})) (ppack (f outv) >>= punpack {inp=i} {out=o})

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




-- Verified pBits
-- lots of hacks here, to emulate "inspect"/"destruct as"
-- and some general mess too

total nat_eqb_eq : (x : Nat) -> (y : Nat) -> (x == y = True) -> (x = y)
nat_eqb_eq Z Z p = refl
nat_eqb_eq Z (S y) p = FalseElim (trueNotFalse (sym p))
nat_eqb_eq (S x) Z p = FalseElim (trueNotFalse (sym p))
nat_eqb_eq (S x) (S y) p = cong {f=S} (nat_eqb_eq x y p)

total beqNatSym : (a : Nat) -> (b : Nat) -> (a == b) = (b == a)
beqNatSym Z Z = refl
beqNatSym Z (S b) = refl
beqNatSym (S a) Z = refl
beqNatSym (S a) (S b) = beqNatSym a b

total beqNatSymImpl : {v : Bool} -> (a : Nat) -> (b : Nat) -> ((a == b) = v) -> ((b == a) = v)
beqNatSymImpl a b eq = trans (beqNatSym b a) eq

total take_len : (n : Nat) -> (l : List a) -> n = length l -> take n l = l
take_len Z [] p = refl
take_len Z (x :: xs) p = FalseElim (OnotS p)
take_len (S k) [] p = refl
take_len (S k) (x :: xs) p = cong {f=(x ::)} $ take_len k xs $ succInjective k (length xs) p

total drop_len : (n : Nat) -> (l : List a) -> n = length l -> drop n l = List.Nil {a=a}
drop_len Z [] p = refl
drop_len Z (x :: xs) p = FalseElim (OnotS p)
drop_len (S k) [] p = FalseElim (OnotS (sym p))
drop_len (S k) (x :: xs) p = drop_len k xs $ succInjective k (length xs) p

total pair : {A : Type} -> {B : Type} -> {a : A} -> {b : B} -> {c : A} -> {d : B} ->
  (a = c) -> (b = d) -> (a, b) = (c, d)
pair ac bd = rewrite ac in cong bd

total vp_pbits_lemma2 : (x : Bool) -> (xs : List Bool) -> (m : Nat) -> (n : Nat) -> (length xs = m) -> (S m = n) ->
  maybe T (\x2 => x2 = (x :: xs, List.Nil {a=Bool}))
  (if (n <= (S (length xs))) then (Just (take n (x :: xs), drop n (x :: xs))) else Nothing)
vp_pbits_lemma2 x xs m n l Smn with (n <= (S (length xs)))
  | True = pair
    (take_len n (x :: xs) (trans (sym Smn) (cong {f=S} (sym l))))
    (drop_len n (x :: xs) (trans (sym Smn) (cong {f=S} (sym l))))
  | False = tt

total vp_pbits_lemma1 : (x : Bool) -> (xs : List Bool) -> (m : Nat) -> (n : Nat) ->
  (S m = n) ->
  (((length xs == m) = True) -> ((m == length xs) = True)) ->
  maybe T (\x2 => x2 = (x :: xs, List.Nil {a=Bool}))
  ((if (length xs == m) then ((Just (x :: xs))) else Nothing) >>= punpack {inp=pBits n} {out=List Bool})
vp_pbits_lemma1 x xs m n Smn lxs with (length xs == m)
  | True = vp_pbits_lemma2 x xs m n (sym $ nat_eqb_eq m (length xs) (lxs refl)) Smn
  | False = tt

total vp_pbits_lemma0 : (x : Bool) -> (xs : List Bool) -> (m : Nat) -> (n : Nat) ->
  (S m = n) ->
  maybe T (\x2 => x2 = (x :: xs, List.Nil {a=Bool}))
  ((if (length xs == m) then ((Just (x :: xs))) else Nothing) >>= punpack {inp=pBits n} {out=List Bool})
vp_pbits_lemma0 x xs m n p = vp_pbits_lemma1 x xs m n p (beqNatSymImpl (length xs) m)

instance VerifiedPackable (pBits n) (List Bool) (mkpBits n) where
  v1 [] = case n of
    Z => refl
    (S m) => tt
  v1 (x :: xs) = case n of
    Z => tt
    (S m) => vp_pbits_lemma0 x xs m (S m) refl
