{-# OPTIONS --rewriting --no-fast-reduce -v commassoc:30 #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

cong : ∀ {A B : Set} (f : A → B) 
    {m n} → m ≡ n → f m ≡ f n
cong f refl = refl

-- this is always not empty
data Bag : Set where
    [zero] : Bag
    zero : Bag → Bag
    suc : Bag → Bag

infixl 20 _++_
_++_ : Bag → Bag → Bag
[zero] ++ ys = zero ys
zero xs ++ ys = zero (xs ++ ys)
xs ++ [zero] = zero xs
xs ++ zero ys = zero (xs ++ ys)
suc xs ++ suc ys = suc (xs ++ ys)

++-[zero] : (xs : Bag) → xs ++ [zero] ≡ zero xs
++-[zero] [zero] = refl
++-[zero] (zero xs) = cong zero (++-[zero] xs)
++-[zero] (suc xs) = refl

++-zero : (xs ys : Bag) → xs ++ (zero ys) ≡ zero (xs ++ ys)
++-zero [zero] ys = refl
++-zero (zero xs) ys = cong zero (++-zero xs ys)
++-zero (suc xs) ys = refl

{-# REWRITE ++-[zero] ++-zero #-}

++-comm : (xs ys : Bag) → xs ++ ys ≡ ys ++ xs
++-comm [zero] ys = refl
++-comm xs [zero] = refl
++-comm xs (zero ys) = cong zero (++-comm xs ys)
++-comm (zero xs) ys = cong zero (++-comm xs ys)
++-comm (suc xs) (suc ys) = cong suc (++-comm xs ys)

++-assoc : (xs ys zs : Bag) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [zero] ys zs = refl
++-assoc xs [zero] zs = refl
++-assoc xs ys [zero] = refl
++-assoc (zero xs) ys zs = cong zero (++-assoc xs ys zs)
++-assoc xs (zero ys) zs = cong zero (++-assoc xs ys zs)
++-assoc xs ys (zero zs) = cong zero (++-assoc xs ys zs)
++-assoc (suc xs) (suc ys) (suc zs) = cong suc (++-assoc xs ys zs)

{-# COMMASSOC ++-comm #-}

infixr 21 _+<_
_+<_ : Nat → Bag → Bag
zero +< xs = xs
suc x +< xs = suc (x +< xs)

+<-dist-++ : (x : Nat) (xs ys : Bag) → x +< (xs ++ ys) ≡ x +< xs ++ x +< ys
+<-dist-++ zero xs ys = refl
+<-dist-++ (suc x) xs ys = cong suc (+<-dist-++ x xs ys)

+<-suc : (x : Nat) (xs : Bag) → x +< suc xs ≡ suc (x +< xs)
+<-suc zero xs = refl
+<-suc (suc x) xs = cong suc (+<-suc x xs)

+<-zero : (x : Nat) (xs : Bag) → x +< zero xs ≡ x +< [zero] ++ x +< xs
+<-zero zero xs = refl
+<-zero (suc x) xs = cong suc (+<-zero x xs)

+<-pack-+ : (x y : Nat) (xs : Bag) → x +< y +< xs ≡ (x + y) +< xs
+<-pack-+ zero y xs = refl
+<-pack-+ (suc x) y xs = cong suc (+<-pack-+ x y xs)

{-# REWRITE +<-dist-++ +<-suc +<-zero +<-pack-+ #-}

bag : Nat → Bag
bag x = x +< [zero]

-- test-comm : ∀ {a b : Nat} → bag a ++ bag b ≡ bag b ++ bag a
-- test-comm = refl

-- data _∈_ : Nat → Bag → Set where
--     proof : ∀ {xs} {x} → x ∈ bag x ++ xs
-- infix 19 _∈_

-- test-member : ∀ {o n m} → m ∈ bag o ++ bag m ++ bag n
-- test-member {o} {n} = proof {bag o ++ bag n}

-- data _⊆_ : Bag → Bag → Set where
--     proof : ∀ {ys} {xs} → xs ⊆ xs ++ ys
-- infix 19 _⊆_

-- test-subseteq : ∀ {m o n} → bag o ++ bag n ⊆ bag o ++ bag m ++ bag n
-- test-subseteq {m} = proof {bag m}

-- -- let us try introducing len

-- len : Bag → Nat
-- len [zero] = 1
-- len (zero xs) = suc (len xs)
-- len (suc xs) = len xs

-- len-dist : ∀ (xs ys : Bag) → len (xs ++ ys) ≡ len xs + len ys
-- len-dist [zero] ys = refl
-- len-dist xs [zero] = refl
-- len-dist (zero xs) ys = cong suc (len-dist xs ys)
-- len-dist xs (zero ys) = cong suc (len-dist xs ys)
-- len-dist (suc xs) (suc ys) = len-dist xs ys

-- {-# REWRITE len-dist #-}

-- -- len-dist results in a sum which is not COMMASSOC, so it is not confluent!! 