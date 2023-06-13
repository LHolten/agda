{-# OPTIONS --rewriting --no-fast-reduce -v tc.inj:20 #-}

module PBag where

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import PlusComm1


infixr 22 _⊕_
_⊕_ : Nat → Nat → Nat
zero ⊕ d = d
suc x ⊕ d = suc (x ⊕ d)

data Compare : Nat → Nat → Set where
    < : {d x : Nat} → Compare x (x ⊕ suc d)
    == : {x : Nat} → Compare x x
    > : {d x : Nat} → Compare (x ⊕ suc d) x

cmp : (x y : Nat) → Compare x y
cmp zero zero = ==
cmp zero (suc y) = <
cmp (suc x) zero = >
cmp (suc x) (suc y) = case (cmp x y) of \where
    == → ==
    (<{d}) → <{d}
    (>{d}) → >{d}

-- postulate
--     cmp> : ∀ x {d} → cmp (x ⊕ suc d) x ≡ > {d}
--     cmp< : ∀ x {d} → cmp x (x ⊕ suc d) ≡ < {d}
--     cmp== : ∀ x → cmp x x ≡ ==
-- {-# REWRITE cmp> cmp< cmp== #-}

infixl 20 _⊔_
infixr 21 _↑_
infixr 22 _∩_
postulate
    Bag : Set
    Ø : Bag
    [zero] : Bag
    -- disjoin union: takes the sum of the number of elements in each bag
    _⊔_ : Bag → Bag → Bag
    _↑_ : Nat → Bag → Bag

    Ø⊔xs : (xs : Bag) → Ø ⊔ xs ≡ xs
    xs⊔Ø : (xs : Bag) → xs ⊔ Ø ≡ xs
    x↑Ø : (x : Nat) → x ↑ Ø ≡ Ø

    ⊔-comm : (xs ys : Bag) → xs ⊔ ys ≡ ys ⊔ xs
    ⊔-assoc : (xs ys zs : Bag) → (xs ⊔ ys) ⊔ zs ≡ xs ⊔ (ys ⊔ zs)
    
    ↑-comb : (x : Nat) (xs ys : Bag) → (x ↑ xs) ⊔ (x ↑ ys) ≡ x ↑ (xs ⊔ ys)
    ↑-dist : (x y : Nat) (xs : Bag) → (x ⊕ y) ↑ xs ≡ x ↑ (y ↑ xs)


{-# REWRITE Ø⊔xs xs⊔Ø x↑Ø ↑-comb ↑-dist #-}
{-# COMMASSOC +comm #-}

bag : Nat → Bag
bag x = x ↑ [zero]

data ⊥ : Set where

postulate
    bag≡Ø : ∀ {x} {@0 xs : Bag} {A : Set} → Ø ≡ bag x ⊔ xs → A
    -- ⊔-inj : ∀ {xs ys} → xs ⊔ ys ≡ xs → ys ≡ Ø
    -- ⊔-inj : ∀ a b c → b ⊔ a ≡ c ⊔ a → b ≡ c
    -- bag-inj : ∀ x y → bag x ≡ bag y → x ≡ y

    -- instersection: takes the minimum number of each element in both bags
    _∩_ : Bag → Bag → Bag
    ∩-Ø : ∀ xs → xs ∩ Ø ≡ Ø
    ∩-comm : (xs ys : Bag) → xs ∩ ys ≡ ys ∩ xs
    ∩-assoc : (xs ys zs : Bag) → (xs ∩ ys) ∩ zs ≡ xs ∩ (ys ∩ zs)


    -- ∩-dist : ∀ x xs ys → x ⊔ (xs ∩ ys) ≡ (x ⊔ xs) ∩ (x ⊔ ys)
    x∩y : ∀ x y → (x ≡ y → ⊥) → bag x ∩ bag y ≡ Ø

    -- ⊔-stuff : ∀ x a b c d → x ≡ a ⊔ b → x ≡ c ⊔ d → x ≡ (a ∪ c) ⊔ (b ∩ d)
    ⊔-step : {@0 b d : Bag} → ∀ {a c} → (a ≡ c → ⊥) → bag c ⊔ d ≡ bag a ⊔ b → d ≡ bag a ⊔ (b ∩ d)

    -- union: takes the maximum number of each element in both bags
    _∪_ : Bag → Bag → Bag
    -- x∪y : ∀ x y → (x ∪ y) ⊓ (x ∩ y) ≡ x ⊔ y
    -- bag x ∪ bag y ≡ bag x ⊔ (bag y - bag x)

    
    
-- {-# REWRITE ∩-comb ∩-Ø #-}
{-# COMMASSOC ⊔-comm #-}
{-# COMMASSOC ∩-comm #-}

_||_ : Bool → Bool → Bool
false || x = x
true || x = true

postulate
    x||true : ∀ x → x || true ≡ true
{-# REWRITE x||true #-}

postulate
    _∈_ : Nat → Bag → Bool
    ∈-dist : ∀ x xs ys → x ∈ (xs ⊔ ys) ≡ (x ∈ xs) || (x ∈ ys)
    x∈Ø : ∀ x → x ∈ Ø ≡ false
    x∈x↑[zero] : ∀ x → x ∈ x ↑ [zero] ≡ true
    x⊕y∈x↑ys : ∀ x y ys → x ⊕ y ∈ x ↑ ys ≡ y ∈ ys
    
    y∉y↑suc-d↑ys : ∀ y d ys → y ∈ y ↑ suc d ↑ ys ≡ false
    suc-d∉[zero] : ∀ d → suc d ∈ [zero] ≡ false

{-# REWRITE ∈-dist x∈Ø x∈x↑[zero] x⊕y∈x↑ys y∉y↑suc-d↑ys suc-d∉[zero] #-}

fdsa : ∀ y d → y ∈ y ↑ suc d ↑ [zero] ≡ false
fdsa y d = refl


_∈'_ : Nat → Bag → Set
x ∈' xs = x ∈ xs ≡ true
