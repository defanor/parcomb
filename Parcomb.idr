module Parcomb

%hide Prelude.Monad.(>>=)
%hide Prelude.Monad.flatten
%hide Prelude.Monad.return

data Parser a = MkParser (Lazy (String -> (Maybe a, String)))

parse : Parser a -> String -> (Maybe a, String)
parse p = case p of
  MkParser x => x
  
class Applicative f => LazyAlternative (f : Type -> Type) where
    empty : f a
    alt : Lazy (f a) -> Lazy (f a) -> f a

class Applicative m => LazyMonad (m : Type -> Type) where
    (>>=)  : Lazy (m a) -> Lazy (a -> m b) -> m b


flatten : LazyMonad m => Lazy (m (m a)) -> m a
flatten a = a >>= id

return : LazyMonad m => a -> m a
return = pure


instance Functor Parser where
  map f p = MkParser $ \str => case (parse p str) of
    (Nothing, rest) => (Nothing, rest)
    (Just x, rest) => (Just (f x), rest)

mutual
  instance Applicative Parser where
    pure a = MkParser $ \str => (Just a, str)
    mf <$> mp = do
      p <- mp
      f <- mf
      return (f p)

  instance LazyMonad Parser where
    p >>= g = MkParser $ \str => case (parse p str) of
      (Nothing, rest) => (Nothing, rest)
      (Just x, rest) => parse ((Force g) x) rest
      
instance LazyAlternative Parser where
  empty = MkParser $ \str => (Nothing, str)
  alt f s = MkParser $ \str => case (parse f str) of
    (Nothing, rest) => parse s str
    (Just x, rest) => (Just x, rest)

fail : Parser a
fail = MkParser $ \str => (Nothing, "")

item : Parser Char
item = MkParser $ \str =>
  case str of
    "" => (Nothing, "")
    _ => (Just (strHead str), strTail str)

sat : (Char -> Bool) -> Parser Char
sat p = do
  c <- item
  if p c
  then return c
  else fail

char : Char -> Parser Char
char c = sat (c ==)

string : String -> Parser String
string "" = return ""
string str = do
  char c
  string cs
  return str
where c = strHead str
      cs = strTail str


cons : Parser a -> Lazy (Parser (List a)) -> (Parser (List a))
cons p pl = do
  a <- p
  r <- pl
  return $ a :: r

many : Parser a -> (Parser (List a))
many p  = alt (cons p (many p)) (return [])

-- mutual
--   many : Parser a -> (Parser (List a))
--   many p = alt (some p) (return [])

--   some : Parser a -> (Parser (List a))
--   some p = do
--     a <- p
--     as <- many p
--     return (a :: as)

