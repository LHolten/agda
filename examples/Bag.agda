{-# OPTIONS --rewriting --no-fast-reduce #-}

open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

cong : ∀ {A B : Set} (f : A → B) 
    {m n} → m ≡ n → f m ≡ f n
cong f refl = refl

Bag = List Nat

inc : Bag → Bag
inc [] = []
inc (x ∷ xs) = suc x ∷ xs

infixl 5 _++_
_++_ : Bag → Bag → Bag
[] ++ ys = ys
(zero ∷ xs) ++ ys = zero ∷ (xs ++ ys)
(suc x ∷ xs) ++ [] = suc x ∷ xs
(suc x ∷ xs) ++ (zero ∷ ys) = zero ∷ ((suc x ∷ xs) ++ ys)
(suc x ∷ xs) ++ (suc y ∷ ys) = inc ((x ∷ xs) ++ (y ∷ ys))

++-[] : (xs : Bag) → xs ++ [] ≡ xs
++-[] [] = refl
++-[] (zero ∷ xs) = cong (_∷_ zero) (++-[] xs)
++-[] (suc x ∷ xs) = refl

++-zero : (xs ys : Bag) → xs ++ (zero ∷ ys) ≡ zero ∷ (xs ++ ys)
++-zero [] ys = refl
++-zero (zero ∷ xs) ys = cong (_∷_ zero) (++-zero xs ys)
++-zero (suc x ∷ xs) ys = refl

{-# REWRITE ++-[] ++-zero #-}

++-inc : (xs : Bag) (y : Nat) (ys : Bag) → (inc xs) ++ (suc y ∷ ys) ≡ inc (xs ++ (y ∷ ys))
++-inc [] y ys = refl
++-inc (x ∷ xs) y ys = refl

++-inc-rev : (x : Nat) (xs : Bag) (ys : Bag) → (suc x ∷ xs) ++ (inc ys) ≡ inc ((x ∷ xs) ++ ys)
++-inc-rev x xs [] = refl
++-inc-rev x xs (y ∷ ys) = refl

{-# REWRITE ++-inc ++-inc-rev #-}

++-comm : (xs ys : Bag) → xs ++ ys ≡ ys ++ xs
++-comm [] ys = refl
++-comm xs [] = refl
++-comm xs (zero ∷ ys) = cong (_∷_ zero) (++-comm xs ys)
++-comm (zero ∷ xs) ys = cong (_∷_ zero) (++-comm xs ys)
++-comm (suc x ∷ xs) (suc y ∷ ys) = cong inc (++-comm (x ∷ xs) (y ∷ ys))

++-assoc : (xs ys zs : Bag) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc xs [] zs = refl
++-assoc xs ys [] = refl
++-assoc (zero ∷ xs) ys zs = cong (_∷_ zero) (++-assoc xs ys zs)
++-assoc xs (zero ∷ ys) zs = cong (_∷_ zero) (++-assoc xs ys zs)
++-assoc xs ys (zero ∷ zs) = cong (_∷_ zero) (++-assoc xs ys zs)
++-assoc (suc x ∷ xs) (suc y ∷ ys) (suc z ∷ zs) = cong inc (++-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs))

{-# COMMASSOC ++-comm #-}

len : Bag → Nat
len [] = zero
len (x ∷ xs) = suc (len xs)

test : ∀ {a b} → len ((a ∷ []) ++ (b ∷ [])) ≡ 2
test = {!   !}

test2 : ∀ {a b} → len (a ∷ b ∷ []) ≡ 2
test2 = refl