import VISD.Binary

test : Syntax d Nat => d (Nat, Nat) Nat
test = (val 1) <*> item
   <|> (val 2) <*> (val 3)

test2 : Syntax d Bool => d (Nat, Bool) Bool
test2 = (nat BE 4) <*> (val True)
    <|> (nat BE 2) <*> (val False)

partial test3 : Syntax d Bool => d (Bool, List Nat) Bool
test3 = (val True) <*> ((ignore False <$> item) *> (many $ nat BE 4))
    <|> (val False) <*> ((ignore True <$> item) *> (many $ nat LE 3))

test4 : Syntax d Bool => d (Vect 2 Nat, Bool) Bool
test4 = rep 2 (nat LE 4) <*> val True
    <|> rep 2 (nat BE 3) <*> val False


main : IO ()
main = do
  putStrLn $ show $ parse test4 [False, False, True, False, True, False, False] >>= compose test4
