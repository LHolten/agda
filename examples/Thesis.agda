{-# OPTIONS --rewriting --no-fast-reduce #-}
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Bag1

data Id : Nat → Set where
    id : (n : Nat) → Id n

-- -- end of thesis stuff
-- resolving meta variables with injectivity analysis
inj1 : (a b : Nat) → Id (a + b)
inj1 a b = id (_ + b)

inj1c : (b : Nat) → Id (1 + b)
inj1c b = id (_ + b)

inj1v : (a : Nat) → Id (a + 1)
inj1v a = id (_ + 1)

inj2 : (a b : Nat) → Id (a + b)
inj2 a b = id (a + _)

inj2v : (b : Nat) → Id (1 + b)
inj2v b = id (1 + _)

inj2c : (a : Nat) → Id (a + 1)
inj2c a = id (a + _)


-- write sorting algorithms with types like this
data Compare : Nat → Nat → Set where
    ≤ : {x d : Nat} → Compare x (x + d)
    ≥ : {x d : Nat} → Compare (x + d) x

inc : {x y : Nat} → Compare x y → Compare (suc x) (suc y)
inc ≤ = ≤
inc ≥ = ≥

cmp : (x y : Nat) → Compare x y
cmp zero y = ≤
cmp x zero = ≥
cmp (suc x) (suc y) = inc (cmp x y)

infixr 5 _∷_
data Sorted : Bag → Set where
    [_] : (n : Nat) → Sorted (n +< [zero])
    _∷_ : (x : Nat) {@0 xb : Bag} → Sorted (x +< xb) 
        → Sorted (x +< [zero] ++ x +< xb)

insert : (x : Nat) {@0 yb : Bag} (ys : Sorted yb) 
    → Sorted (x +< [zero] ++ yb)
insert x [ y ] with cmp x y
... | ≤ = x ∷ [ y ]
... | ≥ = y ∷ [ x ]
insert x (y ∷ ys) with cmp x y
... | ≤ = x ∷ y ∷ ys
... | ≥ = y ∷ insert x ys


test : Sorted _
test = 1 ∷ 3 ∷ 4 ∷ [ 4 ]

-- test2 : (_ : Nat) → Sorted _
-- test2 a = a ∷ [ suc a ]



-- test3 : (a : Nat) → Id (suc a)
-- test3 a = id (a + _)

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