module VerifiedInvertible

%default total
%hide Prelude.Algebra.(<*>)
%hide Prelude.Applicative.(<|>)

-- http://www.informatik.uni-marburg.de/~rendel/unparse/


-- core definitions

data T = tt

data PartIso : Type -> Type -> Type where
  MkPartIso : (to : a -> Maybe b) ->
              (from : b -> Maybe a) ->
              (toFrom : (y : b) -> maybe T (\x => x = y) (from y >>= to)) ->
              (fromTo : (x : a) -> maybe T (\y => y = x) (to x >>= from)) ->
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
    -- these two are identical, would be nice to generalize
    tf y with (inspect $ gFrom y)
      | match Nothing {eq=eq} = rewrite eq in tt
      | match (Just tfy) {eq=eq} = rewrite eq in
        rewrite (maybe_assoc ((Just tfy) >>= fFrom) fTo gTo) in
          case (inspect $ fFrom tfy >>= fTo) of
            match Nothing {eq=eq2} => rewrite eq2 in tt
            match (Just tfy') {eq=eq2} => rewrite eq2 in
              rewrite (replace eq2 {P=(\y => maybe T (\x => x = tfy) y)} (fTF tfy)) in
                rewrite (maybe_unbind gFrom gTo y eq) in (gTF y)
    ft y with (inspect $ fTo y)
      | match Nothing {eq=eq} = rewrite eq in tt
      | match (Just gty) {eq=eq} = rewrite eq in
        rewrite (maybe_assoc ((Just gty) >>= gTo) gFrom fFrom) in
          case (inspect $ gTo gty >>= gFrom) of
            match Nothing {eq=eq2} => rewrite eq2 in tt
            match (Just gty') {eq=eq2} => rewrite eq2 in
              rewrite (replace eq2 {P=(\y => maybe T (\x => x = gty) y)} (gFT gty)) in
                rewrite (maybe_unbind fTo fFrom y eq) in (fFT y)

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

-- this function can't be verified: there's no isomorphism when we are
-- ignoring input; neither can it be changed, because it's quite
-- important to be able to ignore input
ignore : a -> PartIso a ()
ignore x = MkPartIso f g tf ft where
  f : a -> Maybe ()
  f y = Just ()
  g : () -> Maybe a
  g () = Just x
  tf () = refl
  ft y = believe_me (x = y)


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


instance Syntax Printer γ where
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


-- -- rep

-- nilv : PartIso () (Vect 0 a)
-- nilv = MkPartIso (const . Just $ Vect.Nil {a=a})
--                  (\xs => case xs of
--                    [] => Just ()
--                    _ => Nothing)

-- consv : PartIso (a, Vect n a) (Vect (S n) a)
-- consv = MkPartIso c1 c2
--   where c1 (x, xs) = Just (x :: xs)
--         c2 (x :: xs) = Just (x, xs)

-- rep : Syntax d c => (n : Nat) -> d a c -> d (Vect n a) c
-- rep Z p = nilv <$> pure ()
-- rep (S k) p = consv <$> p <*> rep k p


-- -- many

-- nil : PartIso () (List a)
-- nil = MkPartIso c1 c2
--   where
--     c1 () = Just []
--     c2 [] = Just ()
--     c2 (x :: xs) = Nothing

-- cons : PartIso (a, List a) (List a)
-- cons = MkPartIso c1 c2
--   where
--     c1 (x, l) = Just $ x :: l
--     c2 [] = Nothing
--     c2 (x :: xs) = Just (x, xs)

-- partial many : Syntax d c => d a c -> d (List a) c
-- many p = (cons <$> (p <*> (many p)))
--      <|> (nil <$> pure ())


-- -- Various types

-- -- List Bool <-> Nat, with size and endianness

-- data Endianness = BE | LE

-- order : Endianness -> Vect n Bool -> Vect n Bool
-- order BE = reverse
-- order LE = id

-- natToBits : Nat -> Endianness -> (k : Nat) -> Vect k Bool
-- natToBits n e v = order e $ natToBits' n v
--   where natToBits' : Nat -> (k : Nat) -> Vect k Bool
--         natToBits' n Z = []
--         natToBits' Z bits = replicate bits False
--         natToBits' n (S bits) = (mod n 2 /= Z) :: natToBits' (div n 2) bits

-- bitsToNat : Vect n Bool -> Endianness -> Nat
-- bitsToNat v e = bitsToNat' (order e v)
--   where bitsToNat' : Vect k Bool -> Nat
--         bitsToNat' [] = Z
--         bitsToNat' (v :: l) = (if v then 1 else 0) + 2 * bitsToNat' l

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
