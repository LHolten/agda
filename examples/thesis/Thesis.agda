{-# OPTIONS --rewriting --no-fast-reduce #-}
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.List
open import Bag
import Bag1

+zero : ∀ {m} → m + zero ≡ m
+zero {m = zero}  = refl
+zero {m = suc m} = cong suc +zero

+suc : ∀ {m n} → m + (suc n) ≡ suc (m + n)
+suc {m = zero}  = refl
+suc {m = suc m} = cong suc +suc

{-# REWRITE +zero +suc #-}

+comm : (m n : Nat) → m + n ≡ n + m
+comm zero n = refl
+comm m zero = refl
+comm (suc m) (suc n) = cong suc (cong suc (+comm m n))

{-# COMMASSOC +comm #-}
{-# COMMASSOC ++-comm #-}
{-# COMMASSOC Bag1.++-comm #-}

data Singleton : Nat → Set where
    just : (n : Nat) → Singleton n

-- -- end of thesis stuff
-- resolving meta variables with injectivity analysis
-- inj1 : (a b : Nat) → Singleton (a + b)
-- inj1 a b = just (_ + b)

-- inj1c : (b : Nat) → Singleton (1 + b)
-- inj1c b = just (_ + b)

-- inj1v : (a : Nat) → Singleton (a + 1)
-- inj1v a = just (_ + 1)

-- inj2 : (a b : Nat) → Singleton (a + b)
-- inj2 a b = just (a + _)

-- inj2v : (b : Nat) → Singleton (1 + b)
-- inj2v b = just (1 + _)

-- inj2c : (a : Nat) → Singleton (a + 1)
-- inj2c a = just (a + _)


-- write sorting algorithms with types like this
data Compare : Nat → Nat → Set where
    ≤ : {d x : Nat} → Compare x (d + x)
    ≥ : {d x : Nat} → Compare (d + x) x

inc : {x y : Nat} → Compare x y → Compare (suc x) (suc y)
inc (≤{d}) = ≤{d}
inc (≥{d}) = ≥{d}

cmp : (x y : Nat) → Compare x y
cmp zero y = ≤
cmp x zero = ≥
cmp (suc x) (suc y) = inc (cmp x y)

infixr 5 _∷_
data Sorted : Bag → Set where
    [] : Sorted []
    _∷_ : (x : Nat) {@0 xb : Bag} → Sorted (x +< xb) 
        → Sorted (bag x ++ x +< xb)

-- turbofish
infixr 5 _∷<_>_
pattern _∷<_>_ x xb xs = _∷_ x {xb} xs

insert : (x : Nat) {@0 yb : Bag} (ys : Sorted yb) 
    → Sorted (bag x ++ yb)
insert x [] = x ∷< [] > []
insert x (y ∷< yb > ys) with cmp x y
... | ≤{d} = x ∷< bag d ++ d +< yb > y ∷< yb > ys
... | ≥{d} = y ∷< bag d ++ yb > insert x ys

from-list : List Nat → Bag
from-list [] = []
from-list (x ∷ xs) = bag x ++ from-list xs 

insert-sort : (xs : List Nat) → Sorted (from-list xs)
insert-sort [] = []
insert-sort (x ∷ xs) = insert x (insert-sort xs)

{-# TERMINATING #-}
merge : {@0 xb : Bag} (xs : Sorted xb) {@0 yb : Bag} (ys : Sorted yb)
    → Sorted (xb ++ yb)
merge [] ys = ys
merge xs [] = xs
merge (x ∷< xb > xs) (y ∷< yb > ys) with cmp x y
... | ≤{d} = x ∷< xb ++ bag d ++ d +< yb > merge xs (y ∷< yb > ys)
... | ≥{d} = y ∷< bag d ++ d +< xb ++ yb > merge (x ∷< xb > xs) ys



test : Sorted _
test = 1 ∷< [] > []


-- test : Sorted _
-- test = 1 ∷ 3 ∷ 4 ∷ 4 ∷ []

-- test2 : (_ : Nat) → Sorted _
-- test2 a = a ∷ [ suc a ]



-- test3 : (a : Nat) → Singleton (suc a)
-- test3 a = just (a + _)

-- data Sorted' : Nat → Set where
--     [_] : (n : Nat) → Sorted' n
--     -- the order `y + x` is what makes this pass test4 
--     _∷_ : (x : Nat) {y : Nat} → Sorted' (y + x) → Sorted' x

-- test4 : (_ : Nat) → Sorted' _
-- test4 a = zero ∷ a ∷ [ suc a ]

-- sum types (using cubical?)
-- i think it is already possible with postulates

variable
    A B C : Set

data Sum : Set → Set → Set₁ where
    left : A → Sum A B
    right : B → Sum A B
    -- comm : Sum A B ≡ Sum B A
    -- assoc : Sum A (Sum B C) ≡ Sum (Sum A B) C    