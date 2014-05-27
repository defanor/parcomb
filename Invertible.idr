module Invertible

%default total

-- http://www.informatik.uni-marburg.de/~rendel/unparse/

data PartIso α β = MkPartIso (α -> Maybe β) (β -> Maybe α)

class PartIsoFunctor (f : Type -> Type -> Type) where
  (<$>) : PartIso α β -> (f α γ -> f β γ)

inverse : PartIso α β -> PartIso β α
inverse (MkPartIso f g) = MkPartIso g f

apply : PartIso α β -> α -> Maybe β
apply (MkPartIso f g) = f

unapply : PartIso α β -> β -> Maybe α
unapply = Invertible.apply . inverse

class ProductFunctor (f : Type -> Type -> Type) where
  pf : f α γ -> f β γ -> f (α, β) γ

class Alternative (f : Type -> Type -> Type) where
  alt : f α γ -> f α γ -> f α γ
  empty : f α γ

class (PartIsoFunctor δ, ProductFunctor δ, Invertible.Alternative δ) => Syntax (δ : Type -> Type -> Type) γ where
  -- (<$>) :: Iso α β → δ α → δ β
  -- (<∗>) :: δ α → δ β → δ (α, β )
  -- (<|>) :: δ α → δ α → δ α
  -- empty :: δ α
  pure : Eq α => α -> δ α γ
  token : δ γ γ



nilv : PartIso () (Vect 0 α)
nilv = MkPartIso (const . Just $ Vect.Nil {a=α})
                (\xs => case xs of
                   [] => Just ()
                   _ => Nothing)

consv : PartIso (α, Vect n α) (Vect (S n) α)
consv = MkPartIso c1 c2
  where c1 (x, xs) = Just (x :: xs)
        c2 (x :: xs) = Just (x, xs)

times : Syntax δ γ => {n : Nat} -> δ α γ -> δ (Vect n α) γ
times {n} p with (n)
  | Z = (nilv <$> (Invertible.pure ()))
  | (S k) = (consv <$> (p `pf` (times p)))


nil : PartIso () (List α)
nil = MkPartIso (const . Just $ List.Nil {a=α})
                (\xs => case xs of
                   [] => Just ()
                   _ => Nothing)

cons : PartIso (α, List α) (List α)
cons = MkPartIso c1 c2
  where c1 (x, xs) = Just (x :: xs)
        c2 [] = Nothing
        c2 (x :: xs) = Just (x, xs)

many : Syntax δ γ => (max : Nat) -> δ α γ -> δ (List α) γ
many Z _ = nil <$> pure ()
many (S m) p = nil <$> pure ()
        `alt` cons <$> (pf p (many m p))


namespace Colist
  codata Colist : (a : Type) -> Type where
    Nil : Colist a
    (::) : a -> Colist a -> Colist a
    
nil' : PartIso () (Colist α)
nil' = MkPartIso (const . Just $ Colist.Nil {a=α})
                (\xs => case xs of
                   [] => Just ()
                   _ => Nothing)

cons' : PartIso (α, Colist α) (Colist α)
cons' = MkPartIso c1 c2
  where c1 (x, xs) = Just (x :: xs)
        c2 [] = Nothing
        c2 (x :: xs) = Just (x, xs)

-- this leads to stack overflow, most likely lazyness should be added
-- somehow
partial many' : Syntax δ γ => δ α γ -> δ (Colist α) γ
many' p =  nil' <$> pure ()
    `alt` cons' <$> (pf p $ many' p)



data Parser α γ = MkParser (List γ -> List (α, List γ))


parse : Parser α γ -> List γ -> List α
parse (MkParser p) s = [x | (x, _) <- p s]

instance PartIsoFunctor Parser where
  iso <$> (MkParser p) = MkParser (\s => [ (y, s')
                                         | (x, s') <- p s
                                         , y <- toList $ apply iso x])

instance ProductFunctor Parser where
  pf (MkParser p) (MkParser q) = MkParser (\s => [ ((x,y), s )
                                                  | (x, s ) <- p s
                                                  , (y, s ) <- q s])

instance Invertible.Alternative Parser where
  alt (MkParser p) (MkParser q) = MkParser (\s => (p s) ++ (q s))
  empty = MkParser (\s => List.Nil)

instance Syntax Parser γ where
  pure x = MkParser (\s => [(x, s)])
  token = MkParser f
  where
    f [] = []
    f (x :: xs) = [(x, xs)]


data Printer α γ = MkPrinter (α -> Maybe (List γ))

print : Printer α γ -> α -> Maybe (List γ)
print (MkPrinter p) x = p x

instance PartIsoFunctor Printer where
  iso <$> (MkPrinter p) = MkPrinter (\b => unapply iso b >>= p)

instance ProductFunctor Printer where
  pf (MkPrinter p) (MkPrinter q) = MkPrinter (\(x, y) => Just (++) <$> (p x) <$> (q y))

instance Invertible.Alternative Printer where
  alt (MkPrinter p) (MkPrinter q) = MkPrinter $ \s =>
    case (p s) of
      Nothing => (q s)
      x => x
  empty = MkPrinter (\s => Nothing)

instance Syntax Printer γ where
  pure x = MkPrinter (\y =>
    if x == y
    then Just []
    else Nothing)
  token = MkPrinter (\t => Just [t])


-- Invertible.print (times $ (Invertible.pure {α=Bool} {γ=Bool} True)) [True, True]
-- Invertible.parse (times {n=2} $ (Invertible.pure {α=Bool} {γ=Bool} True)) [True, False, False]
-- Invertible.print (times $ (Invertible.token {γ=Bool})) [True, False]
-- Invertible.parse (times {n=3} $ (Invertible.token {γ=Bool})) [True, False, True, False]
-- Invertible.print (many 2 $ pf (Invertible.token {γ=Bool}) (Invertible.pure {α=Bool} {γ=Bool} True)) [True, True, False, True]
-- Invertible.parse (many 3 $ pf (Invertible.token {γ=Bool}) (Invertible.pure {α=Bool} {γ=Bool} True)) [True, False]
