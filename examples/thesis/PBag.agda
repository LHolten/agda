{-# OPTIONS --rewriting --no-fast-reduce -v tc.inj:20 #-}

module PBag where

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Bool
open import PlusComm1


infixr 22 _⊕_
abstract
    _⊕_ : Nat → Nat → Nat
    x ⊕ d = x + d

data Compare : Nat → Nat → Set where
    < : {d x : Nat} → Compare x (x ⊕ suc d)
    == : {x : Nat} → Compare x x
    > : {d x : Nat} → Compare (x ⊕ suc d) x

abstract
    cmp : (x y : Nat) → Compare x y
    cmp zero zero = ==
    cmp zero (suc y) = <
    cmp (suc x) zero = >
    cmp (suc x) (suc y) = case (cmp x y) of \where
        == → ==
        (<{d}) → <{d}
        (>{d}) → >{d}

infixl 20 _∪_
infixr 21 _↑_
infixr 22 _∩_
postulate
    Bag : Set
    Ø : Bag
    [zero] : Bag
    _∪_ : Bag → Bag → Bag
    _↑_ : Nat → Bag → Bag

    Ø∪xs : (xs : Bag) → Ø ∪ xs ≡ xs
    xs∪Ø : (xs : Bag) → xs ∪ Ø ≡ xs
    x↑Ø : (x : Nat) → x ↑ Ø ≡ Ø

    ∪-comm : (xs ys : Bag) → xs ∪ ys ≡ ys ∪ xs
    ∪-assoc : (xs ys zs : Bag) → (xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs)
    
    ↑-comb : (x : Nat) (xs ys : Bag) → (x ↑ xs) ∪ (x ↑ ys) ≡ x ↑ (xs ∪ ys)
    ↑-dist : (x y : Nat) (xs : Bag) → (x ⊕ y) ↑ xs ≡ x ↑ (y ↑ xs)


{-# REWRITE Ø∪xs xs∪Ø x↑Ø ↑-comb ↑-dist #-}
{-# COMMASSOC +comm #-}

bag : Nat → Bag
bag x = x ↑ [zero]

data ⊥ : Set where

postulate
    bag≡Ø : ∀ {x} {@0 xs : Bag} {A : Set} → Ø ≡ bag x ∪ xs → A
    -- ∪-inj : ∀ {xs ys} → xs ∪ ys ≡ xs → ys ≡ Ø
    ∪-inj : ∀ a b c → b ∪ a ≡ c ∪ a → b ≡ c
    bag-inj : ∀ x y → bag x ≡ bag y → x ≡ y

    _∩_ : Bag → Bag → Bag
    ∩-comb : ∀ xs ys zs → zs ∪ (xs ∩ ys) ≡ (xs ∪ zs) ∩ (ys ∪ zs)
    ∩-Ø : ∀ xs → xs ∩ Ø ≡ Ø
    ∩-comm : (xs ys : Bag) → xs ∩ ys ≡ ys ∩ xs
    ∩-assoc : (xs ys zs : Bag) → (xs ∩ ys) ∩ zs ≡ xs ∩ (ys ∩ zs)

    -- ∪-stuff : a ∩ c ≡ Ø → a ∪ b ≡ c ∪ d → d ≡ a ∪ (b ∩ d)
    ∪-step : {@0 b d : Bag} → ∀ {a c} → (a ≡ c → ⊥) → bag c ∪ d ≡ bag a ∪ b → d ≡ bag a ∪ (b ∩ d)
    
    
-- {-# REWRITE ∩-comb ∩-Ø #-}
{-# COMMASSOC ∪-comm #-}
{-# COMMASSOC ∩-comm #-}

-- data WithEff : ∀ (b : Bag) {xs : UnSorted b} (O : Set) → Set₁ where

-- handle : ∀ {b x} {xs : UnSorted b} → WithEff (_) {x ∷ xs} Nat → Nat
-- handle = {!   !}

-- data Element : Bag → Set where
--     just : (x : Nat) → {xs : Bag} → Element (bag x ∪ xs)

-- first : ∀ {x xs ys} → (bag x ∪ xs ≡ ys) → UnSorted ys → Element ys
-- first {x} {xs} p [] = case (bag≡Ø {x} {xs}) p of λ {()}
-- first p (_∷_ x {xb} ys) = just x {xb}

-- first' : ∀ {x xs} → UnSorted (bag x ∪ xs) → Element (bag x ∪ xs)
-- first' {x} {xs} list = first {x} {xs} refl list  