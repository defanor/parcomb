module Parcomb

data Parser a = MkParser (String -> (Maybe a, String))

parse : Parser a -> String -> (Maybe a, String)
parse p = case p of
  MkParser x => x

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

  instance Monad Parser where
    p >>= g = MkParser $ \str => case (parse p str) of
      (Nothing, rest) => (Nothing, rest)
      (Just x, rest) => parse (g x) rest
      
instance Alternative Parser where
  empty = MkParser $ \str => (Nothing, str)
  f <|> s = MkParser $ \str => case (parse f str) of
    (Nothing, rest) => parse s str -- should it be rest or str here?
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

mutual
  many : Parser a -> Parser (List a)
  many p = some p <|> return []

  some : Parser a -> Parser (List a)
  some p = do
    a <- p
    as <- many p
    return (a :: as)

