module VISD.Common

%logging 1
%default total
%hide Prelude.Algebra.(<*>)
%hide Prelude.Applicative.(<|>)
%hide Prelude.Vect.reverse

-- http://www.informatik.uni-marburg.de/~rendel/unparse/


-- core definitions

data PartIso : Type -> Type -> Type where
  MkPartIso : (to : a -> Maybe b) ->
              (from : b -> Maybe a) ->
              (toFrom : (y : b) -> maybe () (\x => to x = Just y) (from y)) ->
              (fromTo : (x : a) -> maybe () (\y => from y = Just x) (to x)) ->
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
inspect x = wi x _ Refl

match : {A : Type} -> {x : A} -> (y : A) -> {eq : x = y} -> Inspect x
match y {eq} = wi _ y eq


maybe_assoc : (x : Maybe a) -> (f : a -> Maybe b) -> (g : b -> Maybe c) -> (x >>= (\y => f y >>= g)) = (x >>= f >>= g)
maybe_assoc Nothing f g = Refl
maybe_assoc (Just x) f g = Refl

maybe_unbind : (f : a -> Maybe b) -> (g : b -> Maybe c) -> (x : a) -> {y : b} ->
  (f x = Just y) -> g y = Just x >>= f >>= g
maybe_unbind f g x eq = rewrite eq in Refl


-- Algebra

infixr 1 >=>
(>=>) : Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
f >=> g = \x => f x >>= g

pId : PartIso a a
pId = MkPartIso (\x => Just x) (\x => Just x) (\x => Refl) (\x => Refl)

(.) : PartIso b c -> PartIso a b -> PartIso a c
(MkPartIso gTo gFrom gTF gFT) . (MkPartIso fTo fFrom fTF fFT) =
  MkPartIso
    (ipc_apply (MkPartIso fTo fFrom fTF fFT) >=> ipc_apply (MkPartIso gTo gFrom gTF gFT))
    (ipc_unapply (MkPartIso gTo gFrom gTF gFT) >=> ipc_unapply (MkPartIso fTo fFrom fTF fFT))
    tf ft
  where
    tf y with (inspect $ (gFrom y))
      | match Nothing {eq} = rewrite eq in ()
      | match (Just z) {eq} = rewrite eq in case (inspect $ fFrom z) of
        match Nothing {eq=eq1} => rewrite eq1 in ()
        match (Just n) {eq=eq1} => rewrite eq1 in
          rewrite (replace eq1 {P=(\pz => maybe () (\x => fTo x = Just z) pz)} (fTF z)) in
            (replace eq {P=(\py => maybe () (\x => gTo x = Just y) py)} (gTF y))
    ft x with (inspect $ (fTo x))
      | match Nothing {eq} = rewrite eq in ()
      | match (Just z) {eq} = rewrite eq in case (inspect $ gTo z) of
        match Nothing {eq=eq1} => rewrite eq1 in ()
        match (Just n) {eq=eq1} => rewrite eq1 in
          rewrite (replace eq1 {P=(\pz => maybe () (\x => gFrom x = Just z) pz)} (gFT z)) in
            (replace eq {P=(\py => maybe () (\y => fFrom y = Just x) py)} (fFT x))

commute : PartIso (a, b) (b, a)
commute = MkPartIso f f (\(a,b) => Refl) (\(a,b) => Refl) where
  f : (c, d) -> Maybe (d, c)
  f (a, b) = Just (b, a)

unit : {a : Type} -> PartIso a (a, ())
unit = MkPartIso f g tf ft where
  f : {a : Type} -> a -> Maybe (a, ())
  f a = Just (a, ())
  g : {a : Type} -> (a, ()) -> Maybe a
  g (a, ()) = Just a
  tf (a, ()) = Refl
  ft a = Refl

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
  tf () = Refl
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
      | match False {eq=eq} = rewrite eq in ()
      | match True {eq=eq} = rewrite eq in
        rewrite eq in Refl

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
    tf [] = Refl
    ft () = Refl

consv : PartIso (a, Vect n a) (Vect (S n) a)
consv = MkPartIso c1 c2 tf ft
  where
    c1 : (a, Vect n a) -> Maybe (Vect (S n) a)
    c1 (x, xs) = Just (x :: xs)
    c2 : (Vect (S n) a) -> Maybe (a, Vect n a)
    c2 (x :: xs) = Just (x, xs)
    tf (x :: xs) = Refl
    ft (a, b) = Refl

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
    tf [] = Refl
    tf (x :: xs) = ()
    ft () = Refl

cons : PartIso (a, List a) (List a)
cons = MkPartIso c1 c2 tf ft
  where
    c1 : (a, List a) -> Maybe (List a)
    c1 (x, l) = Just $ x :: l
    c2 : List a -> Maybe (a, List a)
    c2 [] = Nothing
    c2 (x :: xs) = Just (x, xs)
    tf [] = ()
    tf (x :: xs) = Refl
    ft (x, l) = Refl

partial many : Syntax d c => d a c -> d (List a) c
many p = (cons <$> (p <*> (many p)))
     <|> (nil <$> pure ())
