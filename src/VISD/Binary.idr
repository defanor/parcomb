import VISD.Common

-- List Bool <-> Nat, with size and endianness

data Endianness = BE | LE

snoc : {n : Nat} -> {a : Type} -> (x : a) -> Vect n a -> Vect (S n) a
snoc x [] = [x]
snoc x (y :: xs) = (y :: snoc x xs)

reverse : {n : Nat} -> Vect n a -> Vect n a
reverse [] = []
reverse (x :: xs) = (snoc x (reverse xs))

reverse_snoc : {a : Type} -> {n : Nat} -> (x : a) -> (v : Vect n a) -> reverse (snoc x v) = x :: reverse v
reverse_snoc x [] = Refl
reverse_snoc x (y :: xs) = rewrite (reverse_snoc x xs) in Refl

double_reverse : (v : Vect n a) -> reverse (reverse v) = v
double_reverse [] = Refl
double_reverse (x :: xs) = rewrite (reverse_snoc x (reverse xs)) in
  rewrite (double_reverse xs) in Refl

order : Endianness -> Vect n Bool -> Vect n Bool
order BE v = reverse v
order LE v = v

double_order : (e : Endianness) -> (v : Vect n Bool) -> order e (order e v) = v
double_order BE v = (double_reverse v)
double_order LE v = Refl

div2 : Nat -> Nat
div2 Z = 0
div2 (S Z) = 0
div2 (S (S k)) = div2' (S k)
  where -- a hack for totality checker
    div2' : Nat -> Nat
    div2' Z = 0
    div2' (S n) = S (div2 n)

div2_zero : (k : Nat) -> (lte k (S Z) = True) -> div2 k = Z
div2_zero Z prf = Refl
div2_zero (S Z) prf = Refl
div2_zero (S (S k)) prf = (void (trueNotFalse (sym prf)))

mul2 : Nat -> Nat
mul2 Z = 0
mul2 (S k) = (S (S (mul2 k)))

mul2_n_zero : (n : Nat) -> (mul2 n = Z) -> n = Z
mul2_n_zero Z prf = Refl
mul2_n_zero (S k) prf = void $ OnotS (sym prf)

mul2_zero_n : (n : Nat) -> n = Z -> mul2 n = Z
mul2_zero_n n prf = rewrite prf in Refl

mutual
  even : Nat -> Bool
  even Z = True
  even (S k) = odd k

  odd : Nat -> Bool
  odd Z = False
  odd (S k) = even k

even_inv : (n : Nat) -> (even (S n) = not (even n))
even_inv Z = Refl
even_inv (S Z) = Refl
even_inv (S (S k)) = (even_inv k)

mul2_even : (n : Nat) -> even (mul2 n) = True
mul2_even Z = Refl
mul2_even (S k) = (mul2_even k)

mul2_not_odd : (n : Nat) -> odd (mul2 n) = False
mul2_not_odd Z = Refl
mul2_not_odd (S k) = (mul2_not_odd k)

div2_mul2_n_eq_n : (n : Nat) -> div2 (mul2 n) = n
div2_mul2_n_eq_n Z = Refl
div2_mul2_n_eq_n (S k) = cong {f=S} $ div2_mul2_n_eq_n k

div2_S_mul2_n_eq_n : (n : Nat) -> div2 (S (mul2 n)) = n
div2_S_mul2_n_eq_n Z = Refl
div2_S_mul2_n_eq_n (S k) = cong {f=S} $ div2_S_mul2_n_eq_n k

mul2_div2_even : (n : Nat) -> (even n = True) -> mul2 (div2 n) = n
mul2_div2_even Z prf = Refl
mul2_div2_even (S Z) prf = (void (trueNotFalse (sym prf)))
mul2_div2_even (S (S k)) prf = cong {f=S} $ cong {f=S} (mul2_div2_even k prf)

mul2_div2_eq : (n, m : Nat) -> (even m = True) -> (n = div2 m) -> mul2 n = m
mul2_div2_eq n m evp eqp = rewrite eqp in (mul2_div2_even m evp)

div2_S_even : (n : Nat) -> (even n = True) -> div2 (S n) = div2 n
div2_S_even Z prf = Refl
div2_S_even (S Z) prf = (void (trueNotFalse (sym prf)))
div2_S_even (S (S k)) prf = cong {f=S} (div2_S_even k prf)



natToBitsLe : (k : Nat) -> Nat -> Maybe (Vect k Bool)
natToBitsLe bits Z = Just $ replicate bits False
natToBitsLe Z n = Nothing
natToBitsLe (S bits) n = do
  next <- natToBitsLe bits (div2 n)
  return $ odd n :: next

bitsToNatLe : Vect k Bool -> Nat
bitsToNatLe [] = Z
bitsToNatLe (v :: l) = (if v then 1 else 0) + (mul2 $ bitsToNatLe l)



btnl_zero_step : (xs : Vect k Bool) -> (bitsToNatLe (False :: xs) = Z) -> bitsToNatLe xs = Z
btnl_zero_step xs prf = mul2_n_zero (bitsToNatLe xs) $
  replace {P=(\x => 0 + x = Z)} (plusZeroLeftNeutral (mul2 $ bitsToNatLe xs)) prf

btnl_zero : (n : Nat) -> (v : Vect n Bool) -> bitsToNatLe v = Z -> v = Vect.replicate n False
btnl_zero Z [] prf = Refl
btnl_zero (S k) (False :: xs) prf = cong {f=((Vect.(::)) False)} (btnl_zero k xs (btnl_zero_step xs prf))
btnl_zero (S k) (True :: xs) prf = (void $ OnotS (sym prf))

ntbl_zero : (x : Nat) -> (xs : Vect x Bool) -> natToBitsLe x Z = Just xs -> xs = Vect.replicate x False
ntbl_zero Z [] prf = Refl
ntbl_zero (S n) (y :: xs) prf = 
  rewrite (justInjective (replace {P=(\z => z = Just (y :: xs))} (ntbl_zero' (S n)) prf)) in Refl
  where
    ntbl_zero' : (x : Nat) -> natToBitsLe x Z = Just $ Vect.replicate x False
    ntbl_zero' x = Refl

ntbl_step_false : (n : Nat) -> (xs : Vect n Bool) ->
  natToBitsLe n (bitsToNatLe xs) = Just xs ->
  natToBitsLe (S n) (mul2 (bitsToNatLe xs)) = Just (False :: xs)
ntbl_step_false x xs prf with (bitsToNatLe xs)
  | Z = rewrite (ntbl_zero x xs prf) in Refl
  | S m = rewrite (div2_mul2_n_eq_n (S m)) in
    rewrite prf in
      rewrite (mul2_not_odd m) in Refl

ntbl_step_true : (n : Nat) -> (xs : Vect n Bool) ->
  natToBitsLe n (bitsToNatLe xs) = Just xs ->
  natToBitsLe (S n) (S (mul2 (bitsToNatLe xs))) = Just (True :: xs)  
ntbl_step_true n xs prf = rewrite (mul2_even (bitsToNatLe xs)) in
  rewrite (div2_S_mul2_n_eq_n (bitsToNatLe xs)) in
    rewrite prf in Refl

ntbl_btnl : (k : Nat) -> (v : Vect k Bool) -> natToBitsLe k (bitsToNatLe v) = Just v
ntbl_btnl Z [] = Refl
ntbl_btnl (S n) (x :: xs) with (inspect $ bitsToNatLe xs)
    | match Z {eq=eq} = rewrite eq in
      rewrite (btnl_zero n xs eq) in case (inspect x) of
        match True {eq=eq1} => rewrite eq1 in Refl
        match False {eq=eq1} => rewrite eq1 in Refl
    | match (S m) {eq=eq} = case (inspect x) of
      match True {eq=eq1} => rewrite eq1 in (ntbl_step_true n xs (ntbl_btnl n xs))
      match False {eq=eq1} => rewrite eq1 in (ntbl_step_false n xs (ntbl_btnl n xs))


btnl_rep_false : (k : Nat) -> bitsToNatLe (replicate k False) = Z
btnl_rep_false Z = Refl
btnl_rep_false (S k) = (mul2_zero_n (bitsToNatLe (replicate k False)) (btnl_rep_false k))


btnl_ntbl : (k, n : Nat) -> maybe () (\x => bitsToNatLe x = n) $ natToBitsLe k n
btnl_ntbl k Z = (btnl_rep_false k)
btnl_ntbl Z (S j) = ()
btnl_ntbl (S k) (S j) with (inspect $ natToBitsLe k (div2 (S j)))
  | match Nothing {eq=eq} = rewrite eq in ()
  | match (Just xs) {eq=eq} = rewrite eq in case (inspect $ even j) of
    match True {eq=eq1} => rewrite eq1 in cong {f=S} $ 
      mul2_div2_eq (bitsToNatLe xs) j eq1 $ 
        replace {P=(\p => maybe () (\x => bitsToNatLe x = div2 j) p)}
          (replace {P=(\p => natToBitsLe k p = Just xs)} (div2_S_even j eq1) eq)
          (btnl_ntbl k (div2 j))
    match False {eq=eq1} => rewrite eq1 in
      mul2_div2_eq (bitsToNatLe xs) (S j) (replace {P=(\p => even (S j) = not p)} eq1 (even_inv j)) $
        replace {P=(\p => maybe () ((\x => bitsToNatLe x = div2 (S j))) p)} eq (btnl_ntbl k (div2 $ S j))

just_btnl_ntbl : (k, n : Nat) -> maybe () (\x => Just (bitsToNatLe x) = Just n) $ natToBitsLe k n
just_btnl_ntbl k n with (inspect $ natToBitsLe k n)
      | match Nothing {eq=eq} = rewrite eq in ()
      | match (Just v) {eq=eq} = rewrite eq in cong {f=Just} $ case (btnl_ntbl k n) of
        wojust => replace eq wojust


natLeIso : (k : Nat) -> PartIso (Vect k Bool) Nat
natLeIso k = MkPartIso (Just . bitsToNatLe) (natToBitsLe k) tf ft
  where
    tf n = just_btnl_ntbl k n
    ft v = ntbl_btnl k v


natLe : Syntax d Bool => (k : Nat) -> d Nat Bool
natLe k = natLeIso k <$> rep k item

natToBits : Endianness -> (k : Nat) -> Nat -> Maybe (Vect k Bool)
natToBits e k n = natToBitsLe k n >>= Just . order e

bitsToNat : Endianness -> Vect n Bool -> Maybe Nat
bitsToNat e v = Just $ bitsToNatLe (order e v)

btn_ntb : (k, n : Nat) -> (e : Endianness) -> maybe () (\x => bitsToNat e x = Just n) $ natToBits e k n
btn_ntb k n e with (inspect $ natToBitsLe k n)
  | match Nothing {eq=eq} = rewrite eq in ()
  | match (Just as) {eq=eq} = rewrite eq in rewrite (double_order e as) in
    cong {f=Just} (replace eq {P=(\y => maybe () (\x => bitsToNatLe x = n) y)} (btnl_ntbl k n))

ntb_btn : (k : Nat) -> (e : Endianness) -> (v : Vect k Bool) ->
  maybe () (\x => natToBits e k x = Just v) $ bitsToNat e v
ntb_btn k e v = rewrite (ntbl_btnl k (order e v)) in rewrite (double_order e v) in Refl


natIso : (e : Endianness) -> (k : Nat) -> PartIso (Vect k Bool) Nat
natIso e k = MkPartIso (bitsToNat e) (natToBits e k) tf ft
  where
    tf n = (btn_ntb k n e)
    ft v = (ntb_btn k e v)

nat : Syntax d Bool => Endianness -> Nat -> d Nat Bool
nat endianness size = natIso endianness size <$> rep size item
