{-# OPTIONS --rewriting --no-fast-reduce -v tc.inj.use:20 #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
-- open import PlusComm1

cong : ∀ {A B : Set} (f : A → B) 
    {m n} → m ≡ n → f m ≡ f n
cong f refl = refl


+zero : (m : Nat) → m + zero ≡ m
+zero zero  = refl
+zero (suc m) = cong suc (+zero m)

+suc : (m n : Nat) → m + (suc n) ≡ suc (m + n)
+suc zero n = refl
+suc (suc m) n = cong suc (+suc m n)

{-# REWRITE +zero +suc #-}

+comm : (m n : Nat) → m + n ≡ n + m
+comm zero n = refl
+comm m zero = refl
+comm (suc m) (suc n) = cong suc (cong suc (+comm m n))

{-# COMMASSOC +comm #-}

variable
    d : Nat

-- this is always not empty
data Bag1Leq : Nat →  Set where
    [zero] : Bag1Leq d
    zero : Bag1Leq d → Bag1Leq d
    suc : Bag1Leq d → Bag1Leq (suc d)

infixl 20 _++_
_++_ : Bag1Leq d → Bag1Leq d → Bag1Leq d
[zero] ++ ys = zero ys
zero xs ++ ys = zero (xs ++ ys)
xs ++ [zero] = zero xs
xs ++ zero ys = zero (xs ++ ys)
suc xs ++ suc ys = suc (xs ++ ys)

++-[zero] : (xs : Bag1Leq d) → xs ++ [zero] ≡ zero xs
++-[zero] [zero] = refl
++-[zero] (zero xs) = cong zero (++-[zero] xs)
++-[zero] (suc xs) = refl

++-zero : (xs ys : Bag1Leq d) → xs ++ (zero ys) ≡ zero (xs ++ ys)
++-zero [zero] ys = refl
++-zero (zero xs) ys = cong zero (++-zero xs ys)
++-zero (suc xs) ys = refl

{-# REWRITE ++-[zero] ++-zero #-}

++-comm : (xs ys : Bag1Leq d) → xs ++ ys ≡ ys ++ xs
++-comm [zero] ys = refl
++-comm xs [zero] = refl
++-comm xs (zero ys) = cong zero (++-comm xs ys)
++-comm (zero xs) ys = cong zero (++-comm xs ys)
++-comm (suc xs) (suc ys) = cong suc (++-comm xs ys)

++-assoc : (xs ys zs : Bag1Leq d) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [zero] ys zs = refl
++-assoc xs [zero] zs = refl
++-assoc xs ys [zero] = refl
++-assoc (zero xs) ys zs = cong zero (++-assoc xs ys zs)
++-assoc xs (zero ys) zs = cong zero (++-assoc xs ys zs)
++-assoc xs ys (zero zs) = cong zero (++-assoc xs ys zs)
++-assoc (suc xs) (suc ys) (suc zs) = cong suc (++-assoc xs ys zs)

-- {-# COMMASSOC ++-comm #-}

infixr 21 _+<_
_+<_ : (x : Nat) → Bag1Leq d → Bag1Leq (x + d)
zero +< xs = xs
suc x +< xs = suc (x +< xs)

+<-dist-++ : (x : Nat) (xs ys : Bag1Leq d) → x +< (xs ++ ys) ≡ x +< xs ++ x +< ys
+<-dist-++ zero xs ys = refl
+<-dist-++ (suc x) xs ys = cong suc (+<-dist-++ x xs ys)

+<-suc : (x : Nat) (xs : Bag1Leq d) → x +< suc xs ≡ suc (x +< xs)
+<-suc zero xs = refl
+<-suc (suc x) xs = cong suc (+<-suc x xs)

+<-zero : (x : Nat) (xs : Bag1Leq d) → x +< zero xs ≡ x +< ([zero]{d}) ++ x +< xs
+<-zero zero xs = refl
+<-zero (suc x) xs = cong suc (+<-zero x xs)

+<-pack-+ : (x y : Nat) (xs : Bag1Leq d) → x +< y +< xs ≡ (x + y) +< xs
+<-pack-+ zero y xs = refl
+<-pack-+ (suc x) y xs = cong suc (+<-pack-+ x y xs)

{-# REWRITE +<-dist-++ +<-suc +<-zero +<-pack-+ #-}

bag : (x : Nat) → Bag1Leq (x + d)
bag {d} x = _+<_ x ([zero]{d}) 

data Unordered : {d : Nat} (@0 xb : Bag1Leq d) → Set where
    [_] : {d : Nat} (x : Nat) → Unordered {x + d} (bag {d} x)
    _∷_ : (x : Nat) {xb : Bag1Leq (x + d)} (xs : Unordered xb) → Unordered {x + d} (bag {d} x ++ xb)

data Ordered : {d : Nat} (@0 xb : Bag1Leq d) → Set where
    [_] : {d : Nat} (x : Nat) → Ordered {x + d} (bag {d} x)
    _∷_ : (x : Nat) {xb : Bag1Leq d} (xs : Ordered (x +< xb)) → Ordered {x + d} (bag {d} x ++ (x +< xb))

-- quicksort : {xb : Bag1Leq} → Unordered xb → Ordered xb