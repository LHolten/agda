{-# OPTIONS --rewriting --no-fast-reduce -v commassoc:30 #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

cong : ∀ {A B : Set} (f : A → B) 
    {m n} → m ≡ n → f m ≡ f n
cong f refl = refl

+zero : ∀ {m} → m + zero ≡ m
+zero {m = zero}  = refl
+zero {m = suc m} = cong suc +zero

+suc : ∀ {m n} → m + (suc n) ≡ suc (m + n)
+suc {m = zero}  = refl
+suc {m = suc m} = cong suc +suc

{-# REWRITE +zero +suc #-}

+comm : (x y : Nat) → x + y ≡ y + x
+comm zero y = refl
+comm (suc x) y = cong suc (+comm x y)

+assoc : (x y z : Nat) → (x + y) + z ≡ x + (y + z)
+assoc zero y z = refl
+assoc (suc x) y z = cong suc (+assoc x y z)

{-# COMMASSOC +comm #-}

data Compare : Nat → Nat → Set where
    < : {x : Nat} (d : Nat) → Compare x (suc x + d)
    == : {x : Nat} → Compare x x
    > : {x : Nat} (d : Nat) → Compare (suc x + d) x

inc : {x y : Nat} → Compare x y → Compare (suc x) (suc y)
inc (< d) = < d
inc == = ==
inc (> d) = > d

cmp : (x y : Nat) → Compare x y
cmp zero zero = ==
cmp zero (suc y) = < y
cmp (suc x) zero = > x
cmp (suc x) (suc y) = inc (cmp x y)

inv : {x y : Nat} → Compare x y → Compare y x
inv (< d) = > d
inv == = ==
inv (> d) = < d

inv-inc : {x y : Nat} (c : Compare x y) → inv (inc c) ≡ inc (inv c)
inv-inc (< d) = refl
inv-inc == = refl
inv-inc (> d) = refl

{-# REWRITE inv-inc #-}

cmp-flip : (x y : Nat) → inv (cmp x y) ≡ cmp y x
cmp-flip zero zero = refl
cmp-flip zero (suc y) = refl
cmp-flip (suc x) zero = refl
cmp-flip (suc x) (suc y) = cong inc (cmp-flip x y)


infixr 21 _∷_
data Bag : Set where
    [] : Bag
    _∷_ : Nat → Bag → Bag

infixl 20 _++_
{-# TERMINATING #-}
_++_ : Bag → Bag → Bag
[] ++ ys = ys
xs ++ [] = xs
x ∷ xs ++ y ∷ ys with cmp x y
... | (< d) = x ∷ (xs ++ d ∷ ys)
... | == = x ∷ zero ∷ (xs ++ ys)
... | (> d) = y ∷ (d ∷ xs ++ ys)

++-[] : (xs : Bag) → xs ++ [] ≡ xs
++-[] [] = refl
++-[] (x ∷ xs) = refl

{-# REWRITE ++-[] #-}

++-comm : (xs ys : Bag) → xs ++ ys ≡ ys ++ xs
++-comm [] ys = refl
++-comm xs [] = refl
++-comm (x ∷ xs) (y ∷ ys) with cmp x y
... | (< d) = {!   !}
... | == = {!   !}
... | (> d) = {!   !}




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