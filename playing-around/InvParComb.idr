module InvParComb

%default total

data IPC : (listtype : Type) -> (valtype : Type) -> Type where
  MkIPC : (parse : (List listtype -> Maybe (valtype, List listtype))) -> 
          (compose : (valtype -> Maybe (List listtype))) ->
          IPC listtype valtype

ipc_parse : IPC a b -> List a -> Maybe (b, List a)
ipc_parse (MkIPC p c) = p

ipc_compose : IPC a b -> b -> Maybe (List a)
ipc_compose (MkIPC p c) = c

-- Functor, kind of
ipc_fmap : (fp : a -> b) -> (fc : b -> a) -> IPC c a -> IPC c b
ipc_fmap fp fc (MkIPC parse compose) = MkIPC pf cf
  where
    pf l = do
      (x, rest) <- parse l
      return (fp x, rest)
    cf x = compose $ fc x

-- Almost applicative
ipc_pure : (Eq a, Eq b) => a -> IPC a a
ipc_pure v = MkIPC pf cf
  where
    pf l = Just (v, l)
    cf x = if x == v then Just [v] else Nothing

ipc_empty : IPC a b
ipc_empty = MkIPC (\x => Nothing) (\x => Just $ List.Nil)

ipc_item : IPC a a
ipc_item = MkIPC pf cf
  where
    pf [] = Nothing
    pf (x :: xs) = Just (x, xs)
    cf x = Just [x]

ipc_fail : IPC a a
ipc_fail = MkIPC (const Nothing) (const Nothing)

-- Alternative
mplus : Maybe a -> Lazy (Maybe a) -> Maybe a
mplus Nothing m2 = m2
mplus j m2 = j

ipc_alt : IPC a b -> IPC a b -> IPC a b
ipc_alt (MkIPC p1 c1) (MkIPC p2 c2) = MkIPC pf cf
  where
    pf l = mplus (p1 l) (p2 l)
    cf x = mplus (c1 x) (c2 x)


-- Tuple
ipc_tup : IPC a b -> IPC a c -> IPC a (b, c)
ipc_tup (MkIPC p1 c1) (MkIPC p2 c2) = MkIPC pf cf
  where
   pf l = do
     (x, rest) <- p1 l
     (y, ret) <- p2 rest
     return ((x, y), ret)
   cf (x, y) = do
     l1 <- c1 x
     l2 <- c2 y
     return (l1 ++ l2)


-- Vector
ipc_nilv : IPC a (Vect 0 b)
ipc_nilv = MkIPC pf cf
  where
    pf l = Just $ ([], l)
    cf x = Just []

ipc_consv : IPC a b -> IPC a (Vect n b) -> IPC a (Vect (S n) b)
ipc_consv (MkIPC p1 c1) (MkIPC p2 c2) = MkIPC pf cf
  where
    pf l = do
      (x, rest) <- p1 l
      (xs, ret) <- p2 rest
      return (x :: xs, ret)
    cf (x :: xs) = do
      l1 <- c1 x
      l2 <- c2 xs
      return (l1 ++ l2)

ipc_rep : (n : Nat) -> IPC a b -> IPC a (Vect n b)
ipc_rep Z p = ipc_nilv
ipc_rep (S k) p = ipc_consv p (ipc_rep k p)


-- List
ipc_nil : (Eq a, Eq b) => IPC a (List b)
ipc_nil = MkIPC pf cf
  where
    pf l = Just ([], l)
    cf [] = Just []
    cf l = Nothing

ipc_cons : (Eq a, Eq b) => IPC a b -> Lazy (IPC a (List b)) -> IPC a (List b)
ipc_cons (MkIPC p1 c1) (MkIPC p2 c2) = MkIPC pf cf
  where
    pf l = do
      (x, rest) <- p1 l
      (xs, ret) <- p2 rest
      return (x :: xs, ret)
    cf [] = Nothing
    cf (x :: xs) = do
      l1 <- c1 x
      l2 <- c2 xs
      return (l1 ++ l2)

