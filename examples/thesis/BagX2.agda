{-# OPTIONS --rewriting --no-fast-reduce -v commassoc:30 #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import PlusComm1

case_,_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → A → (A → A → B) → B
case x , y of f = f x y

{-# COMMASSOC +comm #-}
{-# COMMASSOC min-comm #-}

data Difference : Set where
    < : (d : Nat) → Difference
    == : Difference
    > : (d : Nat) → Difference

left : Difference → Nat
left (< d) = zero
left == = zero
left (> d) = suc d

right : Difference → Nat
right (< d) = suc d
right == = zero
right (> d) = zero

dif : (x y : Nat) → Difference
dif zero zero = ==
dif zero (suc y) = < y
dif (suc x) zero = > x
dif (suc x) (suc y) = dif x y

right-dif : (x y : Nat) → x ⊔ y + right (dif x y) ≡ y
right-dif zero zero = refl
right-dif zero (suc y) = refl
right-dif (suc x) zero = refl
right-dif (suc x) (suc y) = cong suc (right-dif x y)

left-dif : (x y : Nat) → x ⊔ y + left (dif x y) ≡ x
left-dif zero zero = refl
left-dif zero (suc y) = refl
left-dif (suc x) zero = refl
left-dif (suc x) (suc y) = cong suc (left-dif x y)

{-# REWRITE right-dif left-dif #-}

data Compare : Nat → Nat → Set where
    lower : (x : Nat) (d : Difference) → Compare (x + left d) (x + right d)

cmp : (x y : Nat) → Compare x y
cmp x y = lower (x ⊔ y) (dif x y) 

dif-x-x : (x : Nat) → dif x x ≡ ==
dif-x-x zero = refl
dif-x-x (suc x) = dif-x-x x

dif-x-suc-x-d : (x d : Nat) → dif x (suc x + d) ≡ < d
dif-x-suc-x-d zero d = refl
dif-x-suc-x-d (suc x) d = dif-x-suc-x-d x d

dif-suc-x-d-x : (x d : Nat) → dif (suc x + d) x ≡ > d
dif-suc-x-d-x zero d = refl
dif-suc-x-d-x (suc x) d = dif-suc-x-d-x x d

-- only this one would be necessary if it worked
-- dif-x-d-t : (x d t : Nat) → dif (x + d) (x + t) ≡ dif d t
-- dif-x-d-t zero d t = refl
-- dif-x-d-t (suc x) d t = dif-x-d-t x d t

{-# REWRITE dif-x-x dif-x-suc-x-d dif-suc-x-d-x #-}
-- {-# REWRITE cmp-x-d-t #-}

infixr 21 _∷_
data Bag : Set where
    [] : Bag
    _∷_ : Nat → Bag → Bag

    
-- test : Nat → Nat → Nat → Nat
-- test x d t = min x (min (suc (x + d)) (suc (x + t)))

-- proof : (x d t : Nat) → test x d t ≡ x
-- proof x d t = refl

inc : Bag → Bag
inc [] = []
inc (x ∷ xs) = suc x ∷ xs

mutual
    infixl 20 _++_
    _++_ : Bag → Bag → Bag
    [] ++ ys = ys
    xs ++ [] = xs
    x ∷ xs ++ y ∷ ys = (x ⊔ y) ∷ (case x , y of λ 
        { zero y → xs ++ y ∷ ys
        ; x zero → x ∷ xs ++ ys
        ; (suc x) (suc y) → {!   !}
        })
    
    -- rest : Nat → Bag → Nat → Bag → Bag
    -- rest zero xs zero ys = zero ∷ (xs ++ ys)
    -- rest zero xs y ys = xs ++ y ∷ ys
    -- rest x xs zero ys = x ∷ xs ++ ys
    -- rest (suc x) xs (suc y) ys = {!   !}

    -- x ∷ xs ++ y ∷ ys = (x ⊔ y) ∷ rest x xs y ys
    -- rest x xs y ys with dif x y
    -- ... | < d = xs ++ suc d ∷ ys
    -- ... | == = zero ∷ (xs ++ ys)
    -- ... | > d = suc d ∷ xs ++ ys

-- ++-[] : (xs : Bag) → xs ++ [] ≡ xs
-- ++-[] [] = refl
-- ++-[] (x ∷ xs) = refl

-- {-# REWRITE ++-[] #-}

-- {-# TERMINATING #-}
-- ++-comm : (xs ys : Bag) → xs ++ ys ≡ ys ++ xs
-- ++-comm [] ys = refl
-- ++-comm xs [] = refl
-- ++-comm (x ∷ xs) (y ∷ ys) = cong (_∷_ (x ⊔ y)) (rest-comm x y xs ys)
--     where
--     rest-comm : (x y : Nat) (xs ys : Bag) → rest x xs y ys ≡ rest y ys x xs
--     rest-comm x y xs ys with cmp x y
--     ... | lower _ (< d) = ++-comm xs (suc d ∷ ys)
--     ... | lower _ == = cong (_∷_ zero) (++-comm xs ys)
--     ... | lower _ (> d) = ++-comm (suc d ∷ xs) ys

-- ++-assoc : (xs ys zs : Bag) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
-- ++-assoc [] ys zs = refl
-- ++-assoc xs [] zs = refl
-- ++-assoc xs ys [] = refl
-- ++-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) with cmp x y | cmp y z | cmp x z
-- ... | lower _ (< d) | yz | lower _ (< t) = {! cong (_∷_ x) (++-assoc xs (suc d ∷ ys) (suc t ∷ zs))  !}
-- ... | lower _ (< d) | yz | lower _ == = {!   !}
-- ... | lower _ (< d) | yz | lower _ (> t) = {!   !}
-- ... | lower _ == | yz | xz = {!   !}
-- ... | lower _ (> d) | yz | xz = {!   !}

-- min : Nat → Nat → Nat
-- min zero y = zero
-- min x zero = zero
-- min (suc x) (suc y) = suc (min x y)

-- min-zero : (x : Nat) → min x zero ≡ zero
-- min-zero zero = refl
-- min-zero (suc x) = refl

-- {-# REWRITE min-zero #-}

-- min-comm : (x y : Nat) → min x y ≡ min y x
-- min-comm zero y = refl
-- min-comm x zero = refl
-- min-comm (suc x) (suc y) = cong suc (min-comm x y)

-- min-assoc : (x y z : Nat) → min (min x y) z ≡ min x (min y z)
-- min-assoc zero y z = refl
-- min-assoc x zero z = refl
-- min-assoc x y zero = refl
-- min-assoc (suc x) (suc y) (suc z) = cong suc (min-assoc x y z)

-- {-# COMMASSOC min-comm #-}

-- min-yeet : (x y : Nat) → min (x + y) y ≡ y
-- min-yeet x zero = refl
-- min-yeet x (suc y) = cong suc (min-yeet x y)

-- {-# REWRITE min-yeet #-}

-- dif : Nat → Nat → Nat
-- dif zero y = y
-- dif x zero = x
-- dif (suc x) (suc y) = dif x y

-- max : Nat → Nat → Nat
-- max x y = min x y + dif x y 