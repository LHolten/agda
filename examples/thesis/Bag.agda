{-# OPTIONS --rewriting --no-fast-reduce -v commassoc:30 #-}

open import Agda.Builtin.Nat
open import PlusComm1
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
import Bag1

-- this is always not empty
data Bag : Set where
    [] : Bag
    just : Bag1.Bag → Bag

infixl 20 _++_
_++_ : Bag → Bag → Bag
[] ++ ys = ys
xs ++ [] = xs
just xs ++ just ys = just (xs Bag1.++ ys)

++-[] : (xs : Bag) → xs ++ [] ≡ xs
++-[] [] = refl
++-[] (just x) = refl

{-# REWRITE ++-[] #-}

++-comm : (xs ys : Bag) → xs ++ ys ≡ ys ++ xs
++-comm [] ys = refl
++-comm xs [] = refl
++-comm (just xs) (just ys) = cong just (Bag1.++-comm xs ys)

++-assoc : (xs ys zs : Bag) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc xs [] zs = refl
++-assoc xs ys [] = refl
++-assoc (just xs) (just ys) (just zs) = cong just (Bag1.++-assoc xs ys zs)

{-# COMMASSOC ++-comm #-}

infixr 21 _+<_
_+<_ : Nat → Bag → Bag
d +< [] = []
d +< just x = just (d Bag1.+< x)

+<-dist-++ : (x : Nat) (xs ys : Bag) → x +< (xs ++ ys) ≡ x +< xs ++ x +< ys
+<-dist-++ x [] ys = refl
+<-dist-++ x xs [] = refl
+<-dist-++ x (just xs) (just ys) = refl

+<-pack-+ : (x y : Nat) (xs : Bag) → x +< y +< xs ≡ (x + y) +< xs
+<-pack-+ x y [] = refl
+<-pack-+ x y (just xs) = refl

{-# REWRITE +<-dist-++ +<-pack-+ #-}

bag : Nat → Bag
bag x = x +< just Bag1.[zero]
