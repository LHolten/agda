{-# OPTIONS --rewriting --no-fast-reduce -v commassoc:30 #-}
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import PlusComm1
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import PBag
-- import Bag1

-- {-# COMMASSOC +comm #-}
{-# COMMASSOC ∪-comm #-}
-- {-# COMMASSOC Bag1.∪-comm #-}

infixr 5 _∷_
data Sorted : @0 Bag → Set where
    [] : Sorted Ø
    _∷_ : (x : Nat) {@0 xb : Bag} → Sorted (x ↑ xb) 
        → Sorted (bag x ∪ x ↑ xb)

data UnSorted : @0 Bag → Set where
    [] : UnSorted Ø
    _∷_ : (x : Nat) {@0 xb : Bag} → UnSorted xb 
        → UnSorted (bag x ∪ xb)


insert : (x : Nat) {@0 yb : Bag} (ys : Sorted yb) 
    → Sorted (bag x ∪ yb)
insert x [] = x ∷ []
insert x (y ∷ ys) = case (cmp x y) of \where
    < → x ∷ y ∷ ys
    == → x ∷ y ∷ ys
    > → y ∷ insert x ys

from-list : List Nat → Bag
from-list [] = Ø
from-list (x ∷ xs) = bag x ∪ from-list xs 

insert-sort : {@0 xb : Bag} (xs : UnSorted xb) → Sorted xb
insert-sort [] = []
insert-sort (x ∷ xs) = insert x (insert-sort xs)

{-# TERMINATING #-}
merge : {@0 xb : Bag} (xs : Sorted xb) {@0 yb : Bag} (ys : Sorted yb)
    → Sorted (xb ∪ yb)
merge [] ys = ys
merge xs [] = xs
merge (x ∷ xs) (y ∷ ys) = case (cmp x y) of \where
    < → x ∷ merge xs (y ∷ ys)
    == → x ∷ merge xs (y ∷ ys)
    > → y ∷ merge (x ∷ xs) ys

data Split : @0 Bag → Set where
    zero : Split Ø
    one : (x : Nat) → Split (bag x)
    two : {@0 xb yb : Bag} (xs : UnSorted xb) (ys : UnSorted yb) 
        → Split (xb ∪ yb)

split : {@0 xb : Bag} (xs : UnSorted xb) → Split xb
split [] = zero
split (x ∷ []) = one x
split (x ∷ y ∷ xys) = case (split xys) of \where
    zero → two (x ∷ []) (y ∷ [])
    (one z) → two (x ∷ z ∷ []) (y ∷ [])
    (two l r) → two (x ∷ l) (y ∷ r)

{-# TERMINATING #-}
merge-sort : {@0 xb : Bag} (xs : UnSorted xb) → Sorted xb
merge-sort xs = case (split xs) of \where
    zero → []
    (one x) → x ∷ []
    (two l r) → merge (merge-sort l) (merge-sort r)

-- test : (n : Nat) → Sorted _
-- test n = n ∷ []


-- turbofish
infixr 5 _∷<_>_
pattern _∷<_>_ x xb xs = _∷_ x {xb} xs

case_to_of_ : ∀ {l₁ l₂} {A : Set l₁} → A → (B : Set l₂) → (A → B) → B
case_to_of_ {l₁} {l₂} {A} c B r = case_of_ {l₁} {l₂} {A} {B} c r

-- data ⊥ : Set where

-- data NotNat (y : Nat) : Set where
--     just : (x : Nat) → (_ : x ≡ y → ⊥) → NotNat y


-- -- find the index of a Nat in an unsorted list
-- find : (x : Nat) {xb : Bag} → UnSorted (bag x ∪ xb) → Nat
-- find x {xb} xs = where-x x (λ _ → Nat)
--     (λ ys → zero)
--     (λ y ys res → suc res)
--     {xb} xs

-- -- pos : Nat
-- -- pos = find 3 {bag 0 ∪ bag 2} (2 ∷ 0 ∷ 3 ∷ [])

data CmpEq (x y : Nat) : Set where
    == : x ≡ y → CmpEq x y
    != : (x ≡ y → ⊥) → CmpEq x y

cmp-eq : (x y : Nat) → CmpEq x y
cmp-eq zero zero = == refl
cmp-eq zero (suc y) = != λ ()
cmp-eq (suc x) zero = != λ ()
cmp-eq (suc x) (suc y) = case (cmp-eq x y) of \where
    (== refl) → == refl
    (!= p) → != \where
        refl → p refl

data Index (x : Nat) : {@0 b : Bag} → UnSorted b → Set where
    here : {@0 b : Bag} {ys : UnSorted b} → Index x (x ∷ ys)
    there : ∀ {y} {@0 b : Bag} {xs : UnSorted b} → Index x xs → Index x (y ∷ xs)

find : (x : Nat) {xb : Bag} → (xs : UnSorted (bag x ∪ xb)) → Index x xs 
find x {xb} ys = find' x {xb} ys refl
    where
    find' : (x : Nat) {@0 xb yb : Bag} → (xs : UnSorted yb) → (yb ≡ bag x ∪ xb) → Index x xs 
    find' x {xb} [] p = bag≡Ø {x} {xb} p
    find' x {xb} (y ∷< yb > ys) q = case (cmp-eq x y) of \where
        (== refl) → here
        (!= p) → there (find' x {xb ∩ yb} ys (∪-step {xb} p q))


postulate
    _∈_ : Nat → Bag → Set
    -- ∈-ind : P
    rule2 : ∀ x yb → x ∈ (bag x ∪ yb)
    rule3 : ∀ x y xb → x ∈ xb → x ∈ (bag y ∪ xb)
    rule4 : ∀ x y xb → (x ≡ y → ⊥) → x ∈ (bag y ∪ xb) → x ∈ xb
    rule1 : ∀ x y yb → bag x ≡ bag y ∪ yb → yb ≡ Ø

data NotIn (x : Nat) : @0 Bag → Set where
    empty : NotIn x [zero]
    andn : (y : Nat) → (x ≡ y → ⊥) → {yb : Bag} → NotIn x yb
        → NotIn x (bag y ∪ yb)

data Pos1 (x : Nat) : (@0 xb : Bag) → UnSorted (bag x ∪ xb) → Set where
    here : {@0 xb : Bag} {xs : UnSorted xb} → Pos1 x xb (x ∷ xs)
    next : {y : Nat} {@0 xb : Bag} {xs : UnSorted (bag x ∪ xb)}
        → Pos1 x xb xs → Pos1 x (bag y ∪ xb) (y ∷ xs)

data Pos (x : Nat) : {@0 xb : Bag} → UnSorted xb → Set where
    nowhere : {@0 xb : Bag} {xs : UnSorted xb} → (x ∈ xb → ⊥) 
        → Pos x xs
    at : {@0 xb : Bag} {xs : UnSorted (bag x ∪ xb)} → Pos1 x xb xs 
        → Pos x xs

data IsIn (x : Nat) (@0 xb : Bag) : Set where
    just : bag x ≡ xb → IsIn x xb
    and : ∀ y {yb} → IsIn x yb → bag y ∪ yb ≡ xb → IsIn x xb

-- not-in : (x y : Nat) (yb : Bag) → (IsIn x yb → ⊥) → (x ≡ y → ⊥) → IsIn x (bag y ∪ yb) → ⊥
-- not-in x y yb pb p (just x₁) = {!   !}
-- not-in x y yb pb p (and y₁ q x₁) = {!   !}

-- pos-suc : {y x : Nat} {@0 xb : Bag} {xs : UnSorted xb} → Pos x xs → Pos x (y ∷ xs)
-- pos-suc {y} (nowhere p) = nowhere \where
--     proof → {!  !}
-- pos-suc (at n) = at (next n)

-- find : (x : Nat) {@0 xb : Bag} → (xs : UnSorted xb) → Pos x xs
-- find x [] = nowhere
-- find x (y ∷ ys) = case (cmp x y) of \where
--     == → at here
--     _ → pos-suc (find x ys)

-- find1 : (x : Nat) {@0 xb : Bag} → (xs : UnSorted (bag x ∪ xb)) → Pos1 x xb xs
-- find1 x ys = {!  !}

-- -- test : Sorted _
-- -- test = 1 ∷ 3 ∷ 4 ∷ 4 ∷ []

-- -- test2 : (_ : Nat) → Sorted _
-- -- test2 a = a ∷ [ suc a ]



-- -- test3 : (a : Nat) → Singleton (suc a)
-- -- test3 a = just (a + _)

-- -- data Sorted' : Nat → Set where
-- --     [_] : (n : Nat) → Sorted' n
-- --     -- the order `y + x` is what makes this pass test4 
-- --     _∷_ : (x : Nat) {y : Nat} → Sorted' (y + x) → Sorted' x

-- -- test4 : (_ : Nat) → Sorted' _
-- -- test4 a = zero ∷ a ∷ [ suc a ]

-- -- sum types (using cubical?)
-- -- i think it is already possible with postulates

-- variable
--     A B C : Set

-- data Sum : Set → Set → Set₁ where
--     left : A → Sum A B
--     right : B → Sum A B
--     -- comm : Sum A B ≡ Sum B A
--     -- assoc : Sum A (Sum B C) ≡ Sum (Sum A B) C          