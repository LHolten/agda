{-# OPTIONS --rewriting --no-fast-reduce -v tc.inj:20 #-}

module PBag where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Unit
open import PlusComm1

infixl 20 _++_
infixr 21 _+<_
postulate
    Bag : Set
    Ø : Bag
    [zero] : Bag
    _++_ : Bag → Bag → Bag
    _+<_ : Nat → Bag → Bag

    l-Ø : (xs : Bag) → Ø ++ xs ≡ xs
    r-Ø : (xs : Bag) → xs ++ Ø ≡ xs
    +<-Ø : (x : Nat) → x +< Ø ≡ Ø
    ++-comm : (xs ys : Bag) → xs ++ ys ≡ ys ++ xs
    ++-assoc : (xs ys zs : Bag) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    
    -- +<-dist : (x : Nat) (xs ys : Bag) → x +< (xs ++ ys) ≡ (x +< xs) ++ (x +< ys)
    -- +<-comb : (x y : Nat) (xs : Bag) → x +< (y +< xs) ≡ (x + y) +< xs

    +<-comb : (x : Nat) (xs ys : Bag) → (x +< xs) ++ (x +< ys) ≡ x +< (xs ++ ys)
    +<-dist : (x y : Nat) (xs : Bag) → (x + y) +< xs ≡ x +< (y +< xs)
    +<-zero : (xs : Bag) → zero +< xs ≡ xs
    -- +<-suc : 

{-# REWRITE l-Ø r-Ø +<-Ø +<-dist +<-comb +<-zero #-}
{-# COMMASSOC ++-comm #-}
{-# COMMASSOC +comm #-}

bag : Nat → Bag
bag x = x +< [zero]
