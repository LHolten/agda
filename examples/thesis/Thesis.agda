{-# OPTIONS --rewriting --no-fast-reduce -v commassoc:30 #-}
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import PlusComm1
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Maybe
open import PBag
-- import Bag1

-- {-# COMMASSOC +comm #-}
{-# COMMASSOC ⊔-comm #-}
-- {-# COMMASSOC Bag1.⊔-comm #-}

infixr 5 _∷_
data Sorted : @0 Bag → Set where
    [] : Sorted Ø
    _∷_ : (x : Nat) {@0 xb : Bag} → Sorted (x ↑ xb) 
        → Sorted (bag x ⊔ x ↑ xb)

data UnSorted : @0 Bag → Set where
    [] : UnSorted Ø
    _∷_ : (x : Nat) {@0 xb : Bag} → UnSorted xb 
        → UnSorted (bag x ⊔ xb)


insert : (x : Nat) {@0 yb : Bag} (ys : Sorted yb) 
    → Sorted (bag x ⊔ yb)
insert x [] = x ∷ []
insert x (y ∷ ys) = case (cmp x y) of \where
    < → x ∷ y ∷ ys
    == → x ∷ y ∷ ys
    > → y ∷ insert x ys

from-list : List Nat → Bag
from-list [] = Ø
from-list (x ∷ xs) = bag x ⊔ from-list xs 

insert-sort : {@0 xb : Bag} (xs : UnSorted xb) → Sorted xb
insert-sort [] = []
insert-sort (x ∷ xs) = insert x (insert-sort xs)

{-# TERMINATING #-}
merge : {@0 xb : Bag} (xs : Sorted xb) {@0 yb : Bag} (ys : Sorted yb)
    → Sorted (xb ⊔ yb)
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
        → Split (xb ⊔ yb)

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

-- test4 : Sorted _
-- test4 = 1 ∷ 3 ∷ 4 ∷ 4 ∷ []

-- test2 : (_ : Nat) → Sorted _
-- test2 a = a ∷ suc a ∷ []

-- data Cond (A : Set) : @0 Bool -> Set where
--     return : {@0 v : Bool} → A → Cond A v
--     nvm : Cond A false

-- _>>=_ : ∀ {@0 v : Bool} {X O} → Cond X v → (X → Cond O v) → Cond O v
-- return x >>= f = f x
-- nvm >>= f = nvm

-- _>>_ : ∀ {@0 v : Bool} {O} -> Cond ⊤ v → Cond O v → Cond O v
-- left >> right = left >>= λ tt → right


data Index (x : Nat) : {@0 xb : Bag} → UnSorted xb → Set where
    here : {@0 xb : Bag} {xs : UnSorted xb} → Index x (x ∷ xs)
    there : ∀ {y} {@0 xb : Bag} {xs : UnSorted xb} → Index x xs → Index x (y ∷ xs)

idx : ∀ x {@0 xb : Bag} → (xs : UnSorted xb) → {{p : x ∈' xb}} → Index x xs
idx y (x ∷ xs) = case (cmp x y) of \where
    < → there (idx y xs)
    == → here
    > → there (idx y xs)

idx2 : ∀ x {@0 xb : Bag} → (xs : UnSorted (xb ⊔ bag x)) -> Index x xs
idx2 x xs = idx x xs

data IndexS : (x : Nat) {@0 xb : Bag} → Sorted xb → Set where
    here : {x : Nat} {@0 xb : Bag} {xs : Sorted (x ↑ xb)} → IndexS x (x ∷ xs)
    there : ∀ {y d} {@0 xb : Bag} {xs : Sorted (y ↑ xb)} → IndexS (y ⊕ d) xs → IndexS (y ⊕ d) (y ∷ xs)

idxS : ∀ x {@0 xb : Bag} → (xs : Sorted xb) → {{p : x ∈' xb}} → IndexS x xs
idxS y (x ∷ xs) = case (cmp x y) of \where
    < → there (idxS y xs)
    == → here

idx-list : ∀ x (xs : List Nat) → {{p : x ∈' from-list xs}} -> Nat
idx-list y (x ∷ xs) = case (cmp x y) of \where
    < → suc (idx-list y xs)
    == → zero
    > → suc (idx-list y xs)

test : idx-list 2 (3 ∷ 2 ∷ 4 ∷ []) ≡ 1
test = refl


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