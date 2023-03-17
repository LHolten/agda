{-# OPTIONS --rewriting --no-fast-reduce -v commassoc:30 #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import PlusComm1

-- cong : ∀ {A B : Set} (f : A → B) 
--     {m n} → m ≡ n → f m ≡ f n
-- cong f refl = refl

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

{-# COMMASSOC +comm #-}

data Compare : Nat → Nat → Set where
    < : {x : Nat} (d : Nat) → Compare x (suc x + d)
    == : {x : Nat} → Compare x x
    > : {x : Nat} (d : Nat) → Compare (suc x + d) x

-- inc : {x y : Nat} → Compare x y → Compare (suc x) (suc y)
-- inc (< d) = < d
-- inc == = ==
-- inc (> d) = > d

raise : (x : Nat) {d t : Nat} → Compare d t → Compare (x + d) (x + t)
raise x (<{t} d) = <{x + t} d
raise x (=={t}) = =={x + t}
raise x (>{t} d) = >{x + t} d

inc : {x y : Nat} → Compare x y → Compare (suc x) (suc y)
inc = raise 1

raise-zero : {d t : Nat} (cmp1 : Compare d t)
    → raise zero cmp1 ≡ cmp1
raise-zero (< d) = refl
raise-zero == = refl
raise-zero (> d) = refl

raise-comb : {d t : Nat} {r1 r2 : Nat} (cmp1 : Compare d t)
    → raise r1 (raise r2 cmp1) ≡ raise (r1 + r2) cmp1
raise-comb (< d) = refl
raise-comb == = refl
raise-comb (> d) = refl

{-# REWRITE raise-zero raise-comb #-}

cmp : (x y : Nat) → Compare x y
cmp zero zero = ==
cmp zero (suc y) = < y
cmp (suc x) zero = > x
cmp (suc x) (suc y) = inc (cmp x y)

-- cmp-x-x : (x : Nat) → cmp x x ≡ ==
-- cmp-x-x zero = refl
-- cmp-x-x (suc x) = cong inc (cmp-x-x x)
cmp-x-x : {x : Nat} (cmp1 : Compare x x) → cmp1 ≡ ==
cmp-x-x cmp1 = {! cmp1 !}

-- cmp-x-suc-x-d : (x d : Nat) → cmp x (suc x + d) ≡ < d
-- cmp-x-suc-x-d zero d = refl
-- cmp-x-suc-x-d (suc x) d = cong inc (cmp-x-suc-x-d x d)

-- cmp-suc-x-d-x : (x d : Nat) → cmp (suc x + d) x ≡ > d
-- cmp-suc-x-d-x zero d = refl
-- cmp-suc-x-d-x (suc x) d = cong inc (cmp-suc-x-d-x x d)

-- cmp-x-d-t : (x d t : Nat) → cmp (x + d) (x + t) ≡ raise x (cmp d t)
-- cmp-x-d-t zero d t = refl
-- cmp-x-d-t (suc x) d t = cong inc (cmp-x-d-t x d t)


-- {-# REWRITE cmp-x-x cmp-x-suc-x-d cmp-suc-x-d-x #-}
-- {-# REWRITE cmp-x-d-t #-}

-- infixr 21 _∷_
-- data Bag : Set where
--     [] : Bag
--     _∷_ : Nat → Bag → Bag

    
-- min : Nat → Nat → Nat
-- min x y = min' (cmp x y)
--     where
--     min' : {x1 x2 : Nat} → Compare x1 x2 → Nat
--     min' (<{x} d) = x
--     min' (=={x}) = x
--     min' (>{x} d) = x

--     min-zero1 : {d : Nat} → (cmp : Compare d zero) → min' cmp ≡ zero
--     min-zero1 == = refl
--     min-zero1 (> d) = refl

--     min-zero2 : {d : Nat} → (cmp : Compare zero d) → min' cmp ≡ zero
--     min-zero2 (< d) = refl
--     min-zero2 == = refl

--     min-suc : {x1 x2 : Nat} → (cmp1 : Compare x1 x2) 
--         → min' (inc cmp1) ≡ suc (min' cmp1)
--     min-suc (< d) = refl
--     min-suc == = refl
--     min-suc (> d) = refl

--     {-# REWRITE min-zero1 min-zero2 min-suc #-}
    
--     min-x-d-t : {x d t : Nat} (cmp1 : Compare (x + d) (x + t)) → min' cmp1 ≡ x + min' (cmp d t)
--     min-x-d-t cmp1 = {! cmp1 !}

--     {-# REWRITE min-x-d-t #-}

-- test : Nat → Nat → Nat → Nat
-- test x d t = min x (min (suc (x + d)) (suc (x + t)))

-- proof : (x d t : Nat) → test x d t ≡ x
-- proof x d t = refl

-- infixl 20 _++_
-- {-# TERMINATING #-}
-- _++_ : Bag → Bag → Bag
-- [] ++ ys = ys
-- xs ++ [] = xs
-- x ∷ xs ++ y ∷ ys = min x y ∷ rest x xs y ys
-- -- x ∷ xs ++ y ∷ ys with cmp x y
-- -- ... | (< d) = x ∷ (xs ++ suc d ∷ ys)
-- -- ... | == = x ∷ zero ∷ (xs ++ ys)
-- -- ... | (> d) = y ∷ (suc d ∷ xs ++ ys)
--     where
--     rest : Nat → Bag → Nat → Bag → Bag
--     rest x xs y ys with cmp x y
--     ... | < d = xs ++ suc d ∷ ys
--     ... | == = zero ∷ (xs ++ ys)
--     ... | > d = suc d ∷ xs ++ ys

-- ++-[] : (xs : Bag) → xs ++ [] ≡ xs
-- ++-[] [] = refl
-- ++-[] (x ∷ xs) = refl

-- {-# REWRITE ++-[] #-}

-- {-# TERMINATING #-}
-- ++-comm : (xs ys : Bag) → xs ++ ys ≡ ys ++ xs
-- ++-comm [] ys = refl
-- ++-comm xs [] = refl
-- ++-comm (x ∷ xs) (y ∷ ys) with cmp x y
-- ... | < d = cong (_∷_ x) (++-comm xs (suc d ∷ ys))
-- ... | == = cong (λ v → x ∷ zero ∷ v) (++-comm xs ys)
-- ... | > d = cong (_∷_ y) (++-comm (suc d ∷ xs) ys)

-- ++-assoc : (xs ys zs : Bag) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
-- ++-assoc [] ys zs = refl
-- ++-assoc xs [] zs = refl
-- ++-assoc xs ys [] = refl
-- ++-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) with cmp x y | cmp y z | cmp x z
-- ... | < d | yz | < t = {! cong (_∷_ x) (++-assoc xs (suc d ∷ ys) (suc t ∷ zs))  !}
-- ... | < d | yz | == = {!   !}
-- ... | < d | yz | > t = {!   !}
-- ... | == | yz | xz = {!   !}
-- ... | > d | yz | xz = {!   !}

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