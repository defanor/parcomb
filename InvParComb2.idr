module InvParComb2

%default total
%hide Prelude.Algebra.(<*>)

-- http://www.informatik.uni-marburg.de/~rendel/unparse/

-- core definitions

data PartIso a b = MkPartIso (a -> Maybe b) (b -> Maybe a)

class PartIsoFunctor (f : Type -> Type -> Type) where
  (<$>) : PartIso a b -> (f a c -> f b c)

class PFunctor (f : Type -> Type -> Type) where
  (<*>) : f a c -> f b c -> f (a, b) c

class PAlternative (f : Type -> Type -> Type) where
  (<|>) : f a c -> Lazy (f a c) -> f a c
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
  (MkParser p) <*> (MkParser q) = MkParser pf
  where
    pf l = do
      (x, rest) <- p l
      (y, ret) <- q rest
      return ((x, y), ret)

instance PAlternative Parser where
  (MkParser p) <|> (MkParser q) = MkParser (\s => mplus (p s) (q s))
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
  (MkPrinter p) <*> (MkPrinter q) = MkPrinter (\(x, y) => Just (++) <$> (p x) <$> (q y))

instance PAlternative Printer where
  (MkPrinter p) <|> (MkPrinter q) = MkPrinter $ \s =>
    case (p s) of
      Nothing => (q s)
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
rep Z p= nilv <$> pure ()
rep (S k) p = consv <$> p <*> rep k p



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
   <|> (val 2) <*> (val 3)

-- compose test (1,2)
-- parse test [2,3]



-- nil : PartIso () (List a)
-- nil = MkPartIso (const . Just $ List.Nil {a=a})
--                 (\xs => case xs of
--                    [] => Just ()
--                    _ => Nothing)

-- cons : PartIso (a, List a) (List a)
-- cons = MkPartIso c1 c2
--   where c1 (x, xs) = Just (x :: xs)
--         c2 [] = Nothing
--         c2 (x :: xs) = Just (x, xs)




-- many : Syntax d c => d a c -> d (List a) c
-- many p = nil <$> pure empty
--     <|> cons <$> (p <*> (many p))

-- many : Syntax d c => (max : Nat) -> d a c -> d (List a) c
-- many Z _ = nil <$> pure ()
-- many (S m) p = nil <$> pure ()
--           <|> cons <$> (p <*> (many m p))




-- -- combinators

-- nilv : PartIso () (Vect 0 α)
-- nilv = MkPartIso (const . Just $ Vect.Nil {a=α})
--                 (\xs => case xs of
--                    [] => Just ()
--                    _ => Nothing)

-- consv : PartIso (α, Vect n α) (Vect (S n) α)
-- consv = MkPartIso c1 c2
--   where c1 (x, xs) = Just (x :: xs)
--         c2 (x :: xs) = Just (x, xs)

-- times : Syntax δ γ => {n : Nat} -> δ α γ -> δ (Vect n α) γ
-- times {n} p with (n)
--   | Z = (nilv <$> (Invertible.pure ()))
--   | (S k) = (consv <$> (p `pf` (times p)))



