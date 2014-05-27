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
  (<*>) : f α γ -> Lazy (f β γ) -> Lazy (f (α, β) γ)

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



nil : PartIso () (Vect 0 α)
nil = MkPartIso (const . Just $ Vect.Nil {a=α})
                (\xs => case xs of
                   [] => Just ()
                   _ => Nothing)

cons : PartIso (α, Vect n α) (Vect (S n) α)
cons = MkPartIso c1 c2
  where c1 (x, xs) = Just (x :: xs)
        c2 (x :: xs) = Just (x, xs)

many : Syntax δ γ => {n : Nat} -> δ α γ -> δ (Vect n α) γ
many {n} p with (n)
  | Z = (nil <$> (Invertible.pure ()))
  | (S k) = (cons <$> (p <*> (many p)))


data Parser α γ = MkParser (List γ -> List (α, List γ))


parse : Parser α γ -> List γ -> List α
parse (MkParser p) s = [x | (x, _) <- p s]

instance PartIsoFunctor Parser where
  iso <$> (MkParser p) = MkParser (\s => [ (y, s')
                                         | (x, s') <- p s
                                         , y <- toList $ apply iso x])

instance ProductFunctor Parser where
  (MkParser p) <*> (MkParser q) = MkParser (\s => [ ((x,y), s )
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
  (MkPrinter p) <*> (MkPrinter q) = MkPrinter (\(x, y) => Just (++) <$> (p x) <$> (q y))

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


main : IO ()
main = do
  putStrLn (show $ Invertible.print (many $ (Invertible.pure {α=Bool} {γ=Bool} True)) [True, True])
  putStrLn (show $ Invertible.parse (many {n=2} $ (Invertible.pure {α=Bool} {γ=Bool} True)) [True, False, False])
  putStrLn (show $ Invertible.print (many $ (Invertible.token {γ=Bool})) [True, False])
  putStrLn (show $ Invertible.parse (many {n=3} $ (Invertible.token {γ=Bool})) [True, False, True, False])
