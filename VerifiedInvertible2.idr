module VerifiedInvertible2

%default total
%hide Prelude.Algebra.(<*>)
%hide Prelude.Applicative.(<|>)

-- http://www.informatik.uni-marburg.de/~rendel/unparse/


-- core definitions

data T = tt

data PartIso : Type -> Type -> Type where
  MkPartIso : (to : a -> Maybe b) ->
              (from : b -> Maybe a) ->
              (toFrom : (y : b) -> maybe T (\x => to x = Just y) (from y)) ->
              (fromTo : (x : a) -> maybe T (\y => from y = Just x) (to x)) ->
              PartIso a b

class PartIsoFunctor (f : Type -> Type -> Type) where
  (<$>) : PartIso a b -> (f a c -> f b c)

class PFunctor (f : Type -> Type -> Type) where
  (<*>) : f a c -> Lazy (f b c) -> f (a, b) c

class PAlternative (f : Type -> Type -> Type) where
  (<|>) : f a c -> Lazy (f a c) -> f a c
  empty : f a c

class (PartIsoFunctor d, PFunctor d, PAlternative d) => Syntax (d : Type -> Type -> Type) c where
  pure : Eq a => a -> d a c
  item : d c c


-- helper functions

ipc_inverse : PartIso a b -> PartIso b a
ipc_inverse (MkPartIso f g tf ft) = MkPartIso g f ft tf

ipc_apply : PartIso a b -> a -> Maybe b
ipc_apply (MkPartIso f g ft ft) = f

ipc_unapply : PartIso a b -> b -> Maybe a
ipc_unapply = ipc_apply . ipc_inverse


-- Inspect and other stuff

data Inspect : a -> Type where
  wi : {A : Type} -> (x : A) -> (y : A) -> (eq: x = y) -> Inspect x
  
inspect : {A : Type} -> (x : A) -> Inspect x
inspect x = wi x _ refl

match : {A : Type} -> {x : A} -> (y : A) -> {eq : x = y} -> Inspect x
match y {eq} = wi _ y eq


maybe_assoc : (x : Maybe a) -> (f : a -> Maybe b) -> (g : b -> Maybe c) -> (x >>= (\y => f y >>= g)) = (x >>= f >>= g)
maybe_assoc Nothing f g = refl
maybe_assoc (Just x) f g = refl

maybe_unbind : (f : a -> Maybe b) -> (g : b -> Maybe c) -> (x : a) -> {y : b} ->
  (f x = Just y) -> g y = Just x >>= f >>= g
maybe_unbind f g x eq = rewrite eq in refl


-- Algebra

infixr 1 >=>
(>=>) : Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
f >=> g = \x => f x >>= g

pId : PartIso a a
pId = MkPartIso (\x => Just x) (\x => Just x) (\x => refl) (\x => refl)

(.) : PartIso b c -> PartIso a b -> PartIso a c
(MkPartIso gTo gFrom gTF gFT) . (MkPartIso fTo fFrom fTF fFT) =
  MkPartIso
    (ipc_apply (MkPartIso fTo fFrom fTF fFT) >=> ipc_apply (MkPartIso gTo gFrom gTF gFT))
    (ipc_unapply (MkPartIso gTo gFrom gTF gFT) >=> ipc_unapply (MkPartIso fTo fFrom fTF fFT))
    tf ft
  where
    tf y with (inspect $ (gFrom y))
      | match Nothing {eq} = rewrite eq in tt
      | match (Just z) {eq} = rewrite eq in case (inspect $ fFrom z) of
        match Nothing {eq=eq1} => rewrite eq1 in tt
        match (Just n) {eq=eq1} => rewrite eq1 in
          rewrite (replace eq1 {P=(\pz => maybe T (\x => fTo x = Just z) pz)} (fTF z)) in
            (replace eq {P=(\py => maybe T (\x => gTo x = Just y) py)} (gTF y))
    ft x with (inspect $ (fTo x))
      | match Nothing {eq} = rewrite eq in tt
      | match (Just z) {eq} = rewrite eq in case (inspect $ gTo z) of
        match Nothing {eq=eq1} => rewrite eq1 in tt
        match (Just n) {eq=eq1} => rewrite eq1 in
          rewrite (replace eq1 {P=(\pz => maybe T (\x => gFrom x = Just z) pz)} (gFT z)) in
            (replace eq {P=(\py => maybe T (\y => fFrom y = Just x) py)} (fFT x))

-- pTup : PartIso a b -> PartIso c d -> PartIso (a, c) (b, d)
-- pTup i j = MkPartIso f g where
--   f (a, b) = case (ipc_apply i a) of
--     Nothing => Nothing
--     Just x => case (ipc_apply j b) of
--       Nothing => Nothing
--       Just y => Just (x, y)
--   g (c, d) = case (ipc_unapply i c) of
--     Nothing => Nothing
--     Just x => case (ipc_unapply j d) of
--       Nothing => Nothing
--       Just y => Just (x, y)

-- associate : PartIso (a, (b, c)) ((a, b), c)
-- associate = MkPartIso f g where
--   f (a, (b, c)) = Just ((a, b), c)
--   g ((a, b), c) = Just (a, (b, c))

commute : PartIso (a, b) (b, a)
commute = MkPartIso f f (\(a,b) => refl) (\(a,b) => refl) where
  f : (c, d) -> Maybe (d, c)
  f (a, b) = Just (b, a)

unit : {a : Type} -> PartIso a (a, ())
unit = MkPartIso f g tf ft where
  f : {a : Type} -> a -> Maybe (a, ())
  f a = Just (a, ())
  g : {a : Type} -> (a, ()) -> Maybe a
  g (a, ()) = Just a
  tf (a, ()) = refl
  ft a = refl

-- *>, <*

infixl 3 *>
(*>) : Syntax d c => d () c -> d a c -> d a c
p *> q = ipc_inverse unit . commute <$> p <*> q

infixl 3 <*
(<*) : Syntax d c => d a c -> d () c -> d a c
p <* q = ipc_inverse unit <$> p <*> q

-- the following function can't be verified: there's no isomorphism
-- when we are ignoring input; neither can it be changed, because it's
-- quite important to be able to ignore input

ignore : a -> PartIso a ()
ignore x = MkPartIso f g tf ft where
  f : a -> Maybe ()
  f y = Just ()
  g : () -> Maybe a
  g () = Just x
  tf () = refl
  ft y = believe_me (Just x = Just y)


-- Parser

data Parser a c = MkParser (List c -> Maybe (a, List c))

parse : Parser a c -> List c -> Maybe a
parse (MkParser p) s = p s >>= pure . fst

instance PartIsoFunctor Parser where
  iso <$> (MkParser p) = MkParser pf
  where
    pf l = do
      (x, rest) <- p l
      y <- ipc_apply iso x
      return (y, rest)

instance PFunctor Parser where
  (MkParser p) <*> mkpq = MkParser pf
  where
    pf l = do
      (x, rest) <- p l
      case mkpq of
        (MkParser q) => do
          (y, ret) <- q rest
          return ((x, y), ret)

instance PAlternative Parser where
  (MkParser p) <|> mkpq = MkParser pf
  where
    pf l = case p l of
      Just x => Just x
      Nothing => case mkpq of
        (MkParser q) => q l
  empty = MkParser (\s => Nothing)

instance Syntax Parser c where
  pure x = MkParser (\s => Just (x, s))
  item = MkParser f
  where
    f [] = Nothing
    f (x :: xs) = Just (x, xs)


-- Printer

data Printer a c = MkPrinter (a -> Maybe (List c))

compose : Printer a c -> a -> Maybe (List c)
compose (MkPrinter p) x = p x

instance PartIsoFunctor Printer where
  iso <$> (MkPrinter p) = MkPrinter (\b => ipc_unapply iso b >>= p)

instance PFunctor Printer where
  (MkPrinter p) <*> mkpq = MkPrinter pf
  where
    pf (x, y) = do
      x' <- p x
      case mkpq of
        (MkPrinter q) => do
          y' <- q y
          return (x' ++ y')

instance PAlternative Printer where
  (MkPrinter p) <|> mkpq = MkPrinter $ \s =>
    case (p s) of
      Nothing => case mkpq of
        (MkPrinter q) => q s
      x => x
  empty = MkPrinter (\s => Nothing)


instance Syntax Printer c where
  pure x = MkPrinter (\y =>
    if x == y
    then Just []
    else Nothing)
  item = MkPrinter (\t => Just [t])


-- Basic parsers/composers

sat : Syntax d a => (a -> Bool) -> d a a
sat {a} p = (MkPartIso check check verify verify) <$> item
  where
    check : a -> Maybe a
    check x = if p x then Just x else Nothing
    verify y with (inspect $ p y)
      | match False {eq=eq} = rewrite eq in tt
      | match True {eq=eq} = rewrite eq in
        rewrite eq in refl

val : (Syntax d a, Eq a) => a -> d a a
val x = sat (== x)


-- rep

nilv : PartIso () (Vect 0 a)
nilv = MkPartIso to from tf ft
  where
    to : () -> Maybe (Vect 0 a)
    to () = Just $ Vect.Nil {a=a}
    from : (Vect 0 a) -> Maybe ()
    from [] = Just () 
    from _ = Nothing
    tf [] = refl
    ft () = refl

consv : PartIso (a, Vect n a) (Vect (S n) a)
consv = MkPartIso c1 c2 tf ft
  where
    c1 : (a, Vect n a) -> Maybe (Vect (S n) a)
    c1 (x, xs) = Just (x :: xs)
    c2 : (Vect (S n) a) -> Maybe (a, Vect n a)
    c2 (x :: xs) = Just (x, xs)
    tf (x :: xs) = refl
    ft (a, b) = refl

rep : Syntax d c => (n : Nat) -> d a c -> d (Vect n a) c
rep Z p = nilv <$> pure ()
rep (S k) p = consv <$> p <*> rep k p


-- many

nil : PartIso () (List a)
nil = MkPartIso c1 c2 tf ft
  where
    c1 : () -> Maybe (List a)
    c1 () = Just []
    c2 : List a -> Maybe ()
    c2 [] = Just ()
    c2 (x :: xs) = Nothing
    tf [] = refl
    tf (x :: xs) = tt
    ft () = refl

cons : PartIso (a, List a) (List a)
cons = MkPartIso c1 c2 tf ft
  where
    c1 : (a, List a) -> Maybe (List a)
    c1 (x, l) = Just $ x :: l
    c2 : List a -> Maybe (a, List a)
    c2 [] = Nothing
    c2 (x :: xs) = Just (x, xs)
    tf [] = tt
    tf (x :: xs) = refl
    ft (x, l) = refl

partial many : Syntax d c => d a c -> d (List a) c
many p = (cons <$> (p <*> (many p)))
     <|> (nil <$> pure ())


-- -- Various types

-- -- List Bool <-> Nat, with size and endianness

data Endianness = BE | LE

order : Endianness -> Vect n Bool -> Vect n Bool
order BE = reverse
order LE = id

natToBits : Nat -> Endianness -> (k : Nat) -> Vect k Bool
natToBits n e v = order e $ natToBits' n v
  where natToBits' : Nat -> (k : Nat) -> Vect k Bool
        natToBits' n Z = []
        natToBits' Z bits = replicate bits False
        natToBits' n (S bits) = (mod n 2 /= Z) :: natToBits' (div n 2) bits

bitsToNat : Vect n Bool -> Endianness -> Nat
bitsToNat v e = bitsToNat' (order e v)
  where bitsToNat' : Vect k Bool -> Nat
        bitsToNat' [] = Z
        bitsToNat' (v :: l) = (if v then 1 else 0) + 2 * bitsToNat' l
        
div2 : Nat -> Nat
div2 Z = 0
div2 (S Z) = 0
div2 (S (S k)) = div2' (S k)
  where -- a hack for totality checker
    div2' : Nat -> Nat
    div2' Z = 0
    div2' (S n) = S (div2 n)

div2_zero : (k : Nat) -> (lte k (S Z) = True) -> div2 k = Z
div2_zero Z prf = refl
div2_zero (S Z) prf = refl
div2_zero (S (S k)) prf = (FalseElim (trueNotFalse (sym prf)))

mul2 : Nat -> Nat
mul2 Z = 0
mul2 (S k) = (S (S (mul2 k)))

mul2_n_zero : (n : Nat) -> (mul2 n = Z) -> n = Z
mul2_n_zero Z prf = refl
mul2_n_zero (S k) prf = FalseElim $ OnotS (sym prf)

mul2_zero_n : (n : Nat) -> n = Z -> mul2 n = Z
mul2_zero_n n prf = rewrite prf in refl

mutual
  even : Nat -> Bool
  even Z = True
  even (S k) = odd k

  odd : Nat -> Bool
  odd Z = False
  odd (S k) = even k

even_inv : (n : Nat) -> (even (S n) = not (even n))
even_inv Z = refl
even_inv (S Z) = refl
even_inv (S (S k)) = (even_inv k)

mul2_even : (n : Nat) -> even (mul2 n) = True
mul2_even Z = refl
mul2_even (S k) = (mul2_even k)

mul2_not_odd : (n : Nat) -> odd (mul2 n) = False
mul2_not_odd Z = refl
mul2_not_odd (S k) = (mul2_not_odd k)

div2_mul2_n_eq_n : (n : Nat) -> div2 (mul2 n) = n
div2_mul2_n_eq_n Z = refl
div2_mul2_n_eq_n (S k) = cong {f=S} $ div2_mul2_n_eq_n k

div2_S_mul2_n_eq_n : (n : Nat) -> div2 (S (mul2 n)) = n
div2_S_mul2_n_eq_n Z = refl
div2_S_mul2_n_eq_n (S k) = cong {f=S} $ div2_S_mul2_n_eq_n k

mul2_div2_even : (n : Nat) -> (even n = True) -> mul2 (div2 n) = n
mul2_div2_even Z prf = refl
mul2_div2_even (S Z) prf = (FalseElim (trueNotFalse (sym prf)))
mul2_div2_even (S (S k)) prf = cong {f=S} $ cong {f=S} (mul2_div2_even k prf)

mul2_div2_eq : (n, m : Nat) -> (even m = True) -> (n = div2 m) -> mul2 n = m
mul2_div2_eq n m evp eqp = rewrite eqp in (mul2_div2_even m evp)

div2_S_even : (n : Nat) -> (even n = True) -> div2 (S n) = div2 n
div2_S_even Z prf = refl
div2_S_even (S Z) prf = (FalseElim (trueNotFalse (sym prf)))
div2_S_even (S (S k)) prf = cong {f=S} (div2_S_even k prf)



natToBitsLe : (k : Nat) -> Nat -> Maybe (Vect k Bool)
natToBitsLe bits Z = Just $ replicate bits False
natToBitsLe Z n = Nothing
natToBitsLe (S bits) n = do
  next <- natToBitsLe bits (div2 n)
  return $ odd n :: next

bitsToNatLe : Vect k Bool -> Nat
bitsToNatLe [] = Z
bitsToNatLe (v :: l) = (if v then 1 else 0) + (mul2 $ bitsToNatLe l)



btnl_zero_step : (xs : Vect k Bool) -> (bitsToNatLe (False :: xs) = Z) -> bitsToNatLe xs = Z
btnl_zero_step xs prf = mul2_n_zero (bitsToNatLe xs) $
  replace {P=(\x => 0 + x = Z)} (plusZeroLeftNeutral (mul2 $ bitsToNatLe xs)) prf

btnl_zero : (n : Nat) -> (v : Vect n Bool) -> bitsToNatLe v = Z -> v = Vect.replicate n False
btnl_zero Z [] prf = refl
btnl_zero (S k) (False :: xs) prf = cong {f=((Vect.(::)) False)} (btnl_zero k xs (btnl_zero_step xs prf))
btnl_zero (S k) (True :: xs) prf = (FalseElim $ OnotS (sym prf))

ntbl_zero : (x : Nat) -> (xs : Vect x Bool) -> natToBitsLe x Z = Just xs -> xs = Vect.replicate x False
ntbl_zero Z [] prf = refl
ntbl_zero (S n) (y :: xs) prf = 
  rewrite (justInjective (replace {P=(\z => z = Just (y :: xs))} (ntbl_zero' (S n)) prf)) in refl
  where
    ntbl_zero' : (x : Nat) -> natToBitsLe x Z = Just $ Vect.replicate x False
    ntbl_zero' x = refl

ntbl_step_false : (n : Nat) -> (xs : Vect n Bool) ->
  natToBitsLe n (bitsToNatLe xs) = Just xs ->
  natToBitsLe (S n) (mul2 (bitsToNatLe xs)) = Just (False :: xs)
ntbl_step_false x xs prf with (bitsToNatLe xs)
  | Z = rewrite (ntbl_zero x xs prf) in refl
  | S m = rewrite (div2_mul2_n_eq_n (S m)) in
    rewrite prf in
      rewrite (mul2_not_odd m) in refl

ntbl_step_true : (n : Nat) -> (xs : Vect n Bool) ->
  natToBitsLe n (bitsToNatLe xs) = Just xs ->
  natToBitsLe (S n) (S (mul2 (bitsToNatLe xs))) = Just (True :: xs)  
ntbl_step_true n xs prf = rewrite (mul2_even (bitsToNatLe xs)) in
  rewrite (div2_S_mul2_n_eq_n (bitsToNatLe xs)) in
    rewrite prf in refl

ntbl_btnl : (k : Nat) -> (v : Vect k Bool) -> natToBitsLe k (bitsToNatLe v) = Just v
ntbl_btnl Z [] = refl
ntbl_btnl (S n) (x :: xs) with (inspect $ bitsToNatLe xs)
    | match Z {eq=eq} = rewrite eq in
      rewrite (btnl_zero n xs eq) in case (inspect x) of
        match True {eq=eq1} => rewrite eq1 in refl
        match False {eq=eq1} => rewrite eq1 in refl
    | match (S m) {eq=eq} = case (inspect x) of
      match True {eq=eq1} => rewrite eq1 in (ntbl_step_true n xs (ntbl_btnl n xs))
      match False {eq=eq1} => rewrite eq1 in (ntbl_step_false n xs (ntbl_btnl n xs))


btnl_rep_false : (k : Nat) -> bitsToNatLe (replicate k False) = Z
btnl_rep_false Z = refl
btnl_rep_false (S k) = (mul2_zero_n (bitsToNatLe (replicate k False)) (btnl_rep_false k))


btnl_ntbl : (k, n : Nat) -> maybe T (\x => bitsToNatLe x = n) $ natToBitsLe k n
btnl_ntbl k Z = (btnl_rep_false k)
btnl_ntbl Z (S j) = tt
btnl_ntbl (S k) (S j) with (inspect $ natToBitsLe k (div2 (S j)))
  | match Nothing {eq=eq} = rewrite eq in tt
  | match (Just xs) {eq=eq} = rewrite eq in case (inspect $ even j) of
    match True {eq=eq1} => rewrite eq1 in cong {f=S} $ 
      mul2_div2_eq (bitsToNatLe xs) j eq1 $ 
        replace {P=(\p => maybe T (\x => bitsToNatLe x = div2 j) p)}
          (replace {P=(\p => natToBitsLe k p = Just xs)} (div2_S_even j eq1) eq)
          (btnl_ntbl k (div2 j))
    match False {eq=eq1} => rewrite eq1 in
      mul2_div2_eq (bitsToNatLe xs) (S j) (replace {P=(\p => even (S j) = not p)} eq1 (even_inv j)) $
        replace {P=(\p => maybe T ((\x => bitsToNatLe x = div2 (S j))) p)} eq (btnl_ntbl k (div2 $ S j))

natBitsLeIso : (k : Nat) -> PartIso Nat (Vect k Bool)
natBitsLeIso k = MkPartIso (natToBitsLe k) (Just . bitsToNatLe) ?tf ?ft




-- nat : Syntax d Bool => Endianness -> Nat -> d Nat Bool
-- nat endianness size = MkPartIso pf cf <$> rep size item
--   where
--     pf l = Just $ bitsToNat l endianness
--     cf x = Just $ natToBits x endianness size


-- testing

test : Syntax d Nat => d (Nat, Nat) Nat
test = (val 1) <*> item
   <|> (val 2) <*> (val 3)

-- test2 : Syntax d Bool => d (Nat, Bool) Bool
-- test2 = (nat BE 4) <*> (val True)
--     <|> (nat BE 2) <*> (val False)

-- partial test3 : Syntax d Bool => d (Bool, List Nat) Bool
-- test3 = (val True) <*> ((ignore False <$> item) *> (many $ nat BE 4))
--     <|> (val False) <*> ((ignore True <$> item) *> (many $ nat LE 3))

-- -- compose test3 (False, [1,2,3])
-- -- parse test3 [False, True, False, False, False, True, False, True, True, False]


-- -- foldl

-- partial driver : (a -> Maybe a) -> (a -> a)
-- driver step state = case step state of
--   Just state' => driver step state'
--   Nothing => state

-- partial iterate : PartIso a a -> PartIso a a
-- iterate step = MkPartIso f g where
--   f = Just . driver (ipc_apply step)
--   g = Just . driver (ipc_unapply step)

-- step : PartIso (a, b) a -> PartIso (a, List b) (a, List b)
-- step i = (pTup i pId) . associate . (pTup pId (ipc_inverse cons))

-- partial foldl : PartIso (a, b) a -> PartIso (a, List b) a
-- foldl i = ipc_inverse unit . (pTup pId (ipc_inverse nil)) . iterate (step i)



-- optimization for nats, but it doesn't really work anyway

-- div2o : Nat -> Nat
-- div2o n = div n 2

-- div2o_div2 : (n : Nat) -> div2o n = div2 n
-- div2o_div2 Z = {--}?div2o_div2_rhs_1
-- div2o_div2 (S Z) = {--}?div2o_div2_rhs_3
-- div2o_div2 (S (S k)) = {--}?div2o_div2_rhs_4

-- mul2o : Nat -> Nat
-- mul2o n = n * 2

-- mul2o_mul2 : (n : Nat) -> mul2o n = mul2 n
-- mul2o_mul2 Z = refl
-- mul2o_mul2 (S k) = cong {f=S} $ cong {f=S} $ mul2o_mul2 k

-- bitsToNatLeO : Vect k Bool -> Nat
-- bitsToNatLeO [] = Z
-- bitsToNatLeO (v :: l) = (if v then 1 else 0) + (mul2o $ bitsToNatLeO l)

-- btnlo : (v : Vect k Bool) -> bitsToNatLeO v = bitsToNatLe v
-- btnlo [] = refl
-- btnlo (x :: xs) = rewrite (mul2o_mul2 (bitsToNatLeO xs)) in
--   rewrite (btnlo xs) in refl

-- natToBitsLeO : (k : Nat) -> Nat -> Maybe (Vect k Bool)
-- natToBitsLeO bits Z = Just $ replicate bits False
-- natToBitsLeO Z n = Nothing
-- natToBitsLeO (S bits) n = do
--   next <- natToBitsLeO bits (div2o n)
--   return $ odd n :: next

-- ntblo : (k : Nat) -> (n : Nat) -> natToBitsLeO k n = natToBitsLe k n
-- ntblo Z Z = refl
-- ntblo Z (S k) = refl
-- ntblo (S k) Z = refl
-- ntblo (S k) (S j) = rewrite (div2o_div2 (S j)) in
--   rewrite (ntblo k (div2 (S j))) in refl

-- ntblo_btnlo : (k : Nat) -> (v : Vect k Bool) -> natToBitsLeO k (bitsToNatLeO v) = Just v
-- ntblo_btnlo k v = rewrite (btnlo v) in
--   rewrite (ntblo k (bitsToNatLe v)) in
--     ntbl_btnl k v

-- btnl_ntblo : (k, n : Nat) -> maybe T (\x => bitsToNatLeO x = n) $ natToBitsLeO k n
-- btnl_ntblo k n = rewrite (ntblo k n) in case (inspect $ natToBitsLe k n) of
--   match Nothing {eq=eq} => rewrite eq in tt
--   match (Just v) {eq=eq} => rewrite eq in rewrite (btnlo v) in case (btnl_ntbl k n) of
--     c => replace {P=(\p => maybe T (\x => bitsToNatLe x = n) p)} eq c
