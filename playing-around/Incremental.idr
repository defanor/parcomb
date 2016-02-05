module Main

mutual
  data Result : (i, r : Type) -> Type where
    Done : Monoid i => i -> r -> Result i r
    Partial : Monoid i => Inf (Parser i r) -> Result i r
    Failure : Monoid i => String -> Result i r

  data Parser : (i, r : Type) -> Type where
    MkParser : ((i -> Result i r)) -> Parser i r

runParser : Parser i r -> ((i -> Result i r))
runParser (MkParser f) = f

implementation Monoid i => Functor (Result i) where
  map f (Done i r) = Done i (f r)
  map f (Partial k) = assert_total (Partial (MkParser $ map f . runParser k))
  map _ f@(Failure s) = f

implementation Monoid i => Functor (Parser i) where
  map f (MkParser k) = MkParser $ (\x => map f $ k x)

implementation Monoid i => Applicative (Parser i) where
  pure x = MkParser (\i => Done i x)
  (MkParser f) <*> g = MkParser $ \i => case f i of
    Done i' f' => case runParser g i' of
      Done i'' r => Done i'' (f' r)
      Partial k => Partial (MkParser $ map f' . runParser k)
      Failure f => Failure f
    Partial k => Failure "trying to use partial"
    Failure f => Failure f

infixl 2 <*>|
(<*>|) : Monoid i => Parser i (a -> b) -> Lazy (Parser i a) -> Parser i b
(<*>|) f g = f <*> g

implementation Monoid i => Monad (Parser i) where
  f >>= g = MkParser $ \i => case runParser f i of
    Done i' f' => runParser (g f') i'
    Partial k => Partial $ k >>= g
    f@(Failure s) => f

interface Applicative f => LazyAlternative (f : Type -> Type) where
  empty : f a
  (<|>) : f a -> Lazy (f a) -> f a

implementation Monoid i => LazyAlternative (Parser i) where
  empty = MkParser . const $ Failure "an alternative is empty"
  f <|> g = MkParser $ \i => case (runParser f i) of
    Failure _ => runParser g i
    Partial k => Partial $ MkParser $ \i' => runParser (f <|> g) (i <+> i')
    done => done

fail : Monoid i => Parser i r
fail = MkParser . const $ Failure ""

item : Parser (List a) a
item = MkParser $ \i => case i of
  [] => Partial item
  (x::xs) => Done xs x

sat : (a -> Bool) -> Parser (List a) a
sat p = do
  i <- item
  if p i then pure i else fail

list : Eq a => List a -> Parser (List a) (List a)
list [] = pure []
list l@(x::xs) = do
  sat (== x)
  list xs
  return l

oneOf : Eq a => List a -> Parser (List a) a
oneOf l = sat (flip elem l)

option : Monoid i => Parser i b -> Parser i (Maybe b)
option p = (Just <$> p) <|> (pure Nothing)

manyTill : Parser (List a) b -> Parser (List a) c -> Parser (List a) (List b)
manyTill p t = option t >>= maybe ((::) <$> p <*>| manyTill p t) (const $ pure [])

many : Parser (List a) b -> Parser (List a) (List b)
many p = option p >>= maybe (pure []) (\x => (::) <$> pure x <*>| many p)

digit : Parser (List Char) Char
digit = oneOf ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

int : Parser (List Char) Int
int = cast . pack <$> many digit

feed : Monoid i => Result i r -> i -> Result i r
feed (Partial k) i = runParser k i
feed (Done i r) i' = Done (i <+> i') r
feed (Failure s) _ = Failure s

-- feed (runParser (manyTill item (sat (== 'v'))) (the (List Char) ['a', 'b'])) ['c', 'v', 'w']
-- feed (runParser int $ unpack "12") $ unpack "34."

parseWith : Monad m => m i -> Parser i r -> m (Result i r)
parseWith r p = do
  v <- r
  case runParser p v of
    Partial k => parseWith r k
    other => pure other

main : IO ()
main = do
  r <- parseWith (unpack <$> getLine) int
  putStrLn $ case r of
    Done i n => show n ++ " / " ++ pack i
    Failure s => "Failure: " ++ s
    _ => "Partial"
