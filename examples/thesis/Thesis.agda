{-# OPTIONS --rewriting --no-fast-reduce -v commassoc:30 #-}
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import PlusComm1
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import PBag
-- import Bag1

-- {-# COMMASSOC +comm #-}
{-# COMMASSOC ++-comm #-}
-- {-# COMMASSOC Bag1.++-comm #-}

-- write sorting algorithms with types like this
data Compare : Nat → Nat → Set where
    ≤ : {d x : Nat} → Compare x (x + d)
    ≥ : {d x : Nat} → Compare (x + d) x

cmp : (x y : Nat) → Compare x y
cmp zero y = ≤
cmp x zero = ≥
cmp (suc x) (suc y) = case (cmp x y) of \where
    (≤{d}) → ≤{d}
    (≥{d}) → ≥{d}

infixr 5 _∷_
data Sorted : (@0 _ : Bag) → Set where
    [] : Sorted Ø
    _∷_ : (x : Nat) {@0 xb : Bag} → Sorted (x +< xb) 
        → Sorted (bag x ++ x +< xb)

data UnSorted : (@0 _ : Bag) → Set where
    [] : UnSorted Ø
    _∷_ : (x : Nat) {@0 xb : Bag} → UnSorted xb 
        → UnSorted (bag x ++ xb)


insert : (x : Nat) {@0 yb : Bag} (ys : Sorted yb) 
    → Sorted (bag x ++ yb)
insert x [] = x ∷ []
insert x (y ∷ ys) = case (cmp x y) of \where
    ≤ → x ∷ y ∷ ys
    ≥ → y ∷ insert x ys

from-list : List Nat → Bag
from-list [] = Ø
from-list (x ∷ xs) = bag x ++ from-list xs 

insert-sort : {@0 xb : Bag} (xs : UnSorted xb) → Sorted xb
insert-sort [] = []
insert-sort (x ∷ xs) = insert x (insert-sort xs)

{-# TERMINATING #-}
merge : {@0 xb : Bag} (xs : Sorted xb) {@0 yb : Bag} (ys : Sorted yb)
    → Sorted (xb ++ yb)
merge [] ys = ys
merge xs [] = xs
merge (x ∷ xs) (y ∷ ys) = case (cmp x y) of \where
    ≤ → x ∷ merge xs (y ∷ ys)
    ≥ → y ∷ merge (x ∷ xs) ys

data Split : (@0 _ : Bag) → Set where
    zero : Split Ø
    one : (x : Nat) → Split (bag x)
    two : {@0 xb yb : Bag} (xs : UnSorted xb) (ys : UnSorted yb) 
        → Split (xb ++ yb)

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

-- take : Nat → List Nat → List Nat
-- take zero xs = []
-- take (suc n) [] = []
-- take (suc n) (x ∷ xs) = x ∷ take n xs

-- skip : Nat → List Nat → List Nat
-- skip zero xs = xs
-- skip (suc n) [] = []
-- skip (suc n) (x ∷ xs) = skip n xs

-- take-skip : (n : Nat) (xs : List Nat) → from-list (take n xs) ++ from-list (skip n xs) ≡ from-list xs
-- take-skip zero xs = refl
-- take-skip (suc n) [] = refl
-- take-skip (suc n) (x ∷ xs) = cong (_++_ (bag x)) (take-skip n xs)

-- {-# REWRITE take-skip #-}


-- {-# TERMINATING #-}
-- merge-sort : (xs : List Nat) → Sorted (from-list xs)
-- merge-sort [] = []
-- merge-sort (x ∷ []) = x ∷ []
-- merge-sort xs = let half = half-len xs in
--     merge (merge-sort (take half xs)) (merge-sort (skip half xs))

test : (n : Nat) → Sorted _
test n = n ∷ []



-- turbofish
infixr 5 _∷<_>_
pattern _∷<_>_ x xb xs = _∷_ x {xb} xs



postulate
    where-x : (x : Nat)
            → (P : {@0 xb : Bag} → UnSorted (bag x ++ xb) → Set)
            → (left : {@0 yb : Bag} (ys : UnSorted yb) → P {yb} (x ∷ ys))
            → (right : (y : Nat) 
                     → {@0 yb : Bag} (ys : UnSorted (bag x ++ yb)) 
                     → P {yb} ys
                     → P {bag y ++ yb} (y ∷ ys))
            → {@0 xb : Bag} → (xs : UnSorted (bag x ++ xb))
            → P {xb} xs

    left-rule : (x : Nat)
              → (P : {@0 xb : Bag} → UnSorted (bag x ++ xb) → Set)
              → (left : {@0 yb : Bag} (ys : UnSorted yb) → P (x ∷ ys))
              → (right : (y : Nat) 
                       → {@0 yb : Bag} (ys : UnSorted (bag x ++ yb)) 
                       → P {yb} ys
                       → P (y ∷ ys))
              → {@0 yb : Bag} (ys : UnSorted yb)
              → where-x x _ left right (x ∷ ys) ≡ left ys
    
    -- this actually should check that left rule does not apply first
    -- in order to preserve confluence
    right-rule : (x : Nat)
               → (P : {@0 xb : Bag} → UnSorted (bag x ++ xb) → Set)
               → (left : {@0 yb : Bag} (ys : UnSorted yb) → P (x ∷ ys))
               → (right : (y : Nat) 
                        → {@0 yb : Bag} (ys : UnSorted (bag x ++ yb)) 
                        → P {yb} ys
                        → P (y ∷ ys))
               → (y : Nat)
               → {@0 yb : Bag} (ys : UnSorted (bag x ++ yb)) 
               → where-x x _ left right (y ∷ ys) ≡ right y {yb} ys (where-x x _ left right ys)

-- {-# REWRITE left-rule right-rule #-}

-- data ⊥ : Set where

-- data NotNat (y : Nat) : Set where
--     just : (x : Nat) → (_ : x ≡ y → ⊥) → NotNat y


-- -- find the index of a Nat in an unsorted list
-- find : (x : Nat) {xb : Bag} → UnSorted (bag x ++ xb) → Nat
-- find x {xb} xs = where-x x (λ _ → Nat)
--     (λ ys → zero)
--     (λ y ys res → suc res)
--     {xb} xs

-- -- pos : Nat
-- -- pos = find 3 {bag 0 ++ bag 2} (2 ∷ 0 ∷ 3 ∷ [])


-- -- find : (x : Nat) {xb : Bag} → UnSorted (bag x ++ xb) → Nat
-- -- find x (x ∷ ys) = zero
-- -- find x (y ∷ ys) = suc (find x ys)




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