module InvParComb2

%default total
%hide Prelude.Algebra.(<*>)

-- http://www.informatik.uni-marburg.de/~rendel/unparse/

-- core definitions

data PartIso a b = MkPartIso (a -> Maybe b) (b -> Maybe a)

class PartIsoFunctor (f : Type -> Type -> Type) where
  (<$>) : PartIso a b -> (f a c -> f b c)

class PFunctor (f : Type -> Type -> Type) where
  (<*>) : f a c -> Lazy (f b c) -> f (a, b) c

infixl 3 <||>
class PAlternative (f : Type -> Type -> Type) where
  (<||>) : f a c -> Lazy (f a c) -> f a c
  empty : f a c

class (PartIsoFunctor d, PFunctor d, PAlternative d) => Syntax (d : Type -> Type -> Type) c where
  pure : Eq a => a -> d a c
  item : d c c


-- helper functions
ipc_inverse : PartIso a b -> PartIso b a
ipc_inverse (MkPartIso f g) = MkPartIso g f

ipc_apply : PartIso a b -> a -> Maybe b
ipc_apply (MkPartIso f g) = f

ipc_unapply : PartIso a b -> b -> Maybe a
ipc_unapply = ipc_apply . ipc_inverse

mplus : Maybe a -> Lazy (Maybe a) -> Maybe a
mplus Nothing m2 = m2
mplus j m2 = j


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
  (MkParser p) <||> mkpq = MkParser pf
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
  (MkPrinter p) <||> mkpq = MkPrinter $ \s =>
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
sat p = (MkPartIso check check) <$> item
  where check x = if p x then Just x else Nothing

val : (Syntax d a, Eq a) => a -> d a a
val x = sat (== x)


-- rep

nilv : PartIso () (Vect 0 a)
nilv = MkPartIso (const . Just $ Vect.Nil {a=a})
                 (\xs => case xs of
                   [] => Just ()
                   _ => Nothing)

consv : PartIso (a, Vect n a) (Vect (S n) a)
consv = MkPartIso c1 c2
  where c1 (x, xs) = Just (x :: xs)
        c2 (x :: xs) = Just (x, xs)

rep : Syntax d c => (n : Nat) -> d a c -> d (Vect n a) c
rep Z p = nilv <$> pure ()
rep (S k) p = consv <$> p <*> rep k p


-- many

nil : PartIso () (List a)
nil = MkPartIso c1 c2
  where
    c1 () = Just []
    c2 [] = Just ()
    c2 (x :: xs) = Nothing

cons : PartIso (a, List a) (List a)
cons = MkPartIso c1 c2
  where
    c1 (x, l) = Just $ x :: l
    c2 [] = Nothing
    c2 (x :: xs) = Just (x, xs)

partial many : Syntax d c => d a c -> d (List a) c
many p = (cons <$> (p <*> (many p)))
    <||> (nil <$> pure ())


-- Various types

-- Binary <-> Nat
natToBits : Nat -> (k : Nat) -> Vect k Bool
natToBits n v = reverse $ natToBits' n v
  where natToBits' : Nat -> (k : Nat) -> Vect k Bool
        natToBits' n Z = []
        natToBits' Z bits = replicate bits False
        natToBits' n (S bits) = (mod n 2 /= Z) :: natToBits' (div n 2) bits

bitsToNat : Vect n Bool -> Nat
bitsToNat v = bitsToNat' (reverse v)
  where bitsToNat' : Vect k Bool -> Nat
        bitsToNat' [] = Z
        bitsToNat' (v :: l) = (if v then 1 else 0) + 2 * bitsToNat' l

nat : Syntax d Bool => Nat -> d Nat Bool
nat size = MkPartIso pf cf <$> rep size item
  where
    pf l = Just $ bitsToNat l
    cf x = Just $ natToBits x size


-- testing

test : Syntax d Nat => d (Nat, Nat) Nat
test = (val 1) <*> item
  <||> (val 2) <*> (val 3)

test2 : Syntax d Bool => d (Nat, Bool) Bool
test2 = (nat 4) <*> (val True)
   <||> (nat 2) <*> (val False)

-- compose test (1,2)
-- parse test [2,3]



-- Algebra, foldl

infixr 1 >=>
(>=>) : Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
f >=> g = \x => f x >>= g

pId : PartIso a a
pId = MkPartIso (\x => Just x) (\x => Just x)

(.) : PartIso b c -> PartIso a b -> PartIso a c
g . f = MkPartIso (ipc_apply f >=> ipc_apply g) (ipc_unapply g >=> ipc_unapply f)


pTup : PartIso a b -> PartIso c d -> PartIso (a, c) (b, d)
pTup i j = MkPartIso f g where
  f (a, b) = case (ipc_apply i a) of
    Nothing => Nothing
    Just x => case (ipc_apply j b) of
      Nothing => Nothing
      Just y => Just (x, y)
  g (c, d) = case (ipc_unapply i c) of
    Nothing => Nothing
    Just x => case (ipc_unapply j d) of
      Nothing => Nothing
      Just y => Just (x, y)

associate : PartIso (a, (b, c)) ((a, b), c)
associate = MkPartIso f g where
  f (a, (b, c)) = Just ((a, b), c)
  g ((a, b), c) = Just (a, (b, c))

commute : PartIso (a, b) (b, a)
commute = MkPartIso f f where
  f : (c, d) -> Maybe (d, c)
  f (a, b) = Just (b, a)

unit : PartIso a (a, ())
unit = MkPartIso f g where
  f a = Just (a, ())
  g (a, ()) = Just a


partial driver : (a -> Maybe a) -> (a -> a)
driver step state = case step state of
  Just state' => driver step state'
  Nothing => state

partial iterate : PartIso a a -> PartIso a a
iterate step = MkPartIso f g where
  f = Just . driver (ipc_apply step)
  g = Just . driver (ipc_unapply step)

step : PartIso (a, b) a -> PartIso (a, List b) (a, List b)
step i = (pTup i pId) . associate . (pTup pId (ipc_inverse cons))

partial foldl : PartIso (a, b) a -> PartIso (a, List b) a
foldl i = ipc_inverse unit . (pTup pId (ipc_inverse nil)) . iterate (step i)
