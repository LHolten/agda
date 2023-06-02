{-# OPTIONS --rewriting --no-fast-reduce -v commassoc:20 #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Unit


cong : ∀ { a b} { A : Set a }  { B : Set b }
       (f : A → B ) {m  n}  → m ≡ n → f m ≡ f n
cong f refl = refl

case_of_ : ∀ {l₁ l₂} {A : Set l₁} {B : Set l₂} → A → (A → B) → B
case x of f = f x

+zero : ∀ {m} → m + zero ≡ m
+zero {m = zero}  = refl
+zero {m = suc m} = cong suc +zero

+suc : (m n : Nat) → m + (suc n) ≡ suc (m + n)
+suc zero n  = refl
+suc (suc m) n = cong suc (+suc m n)

{-# REWRITE +zero +suc #-}

+comm : (x y : Nat) → x + y ≡ y + x
+comm zero y = refl
+comm (suc x) y = cong suc (+comm x y)

+assoc : (x y z : Nat) → (x + y) + z ≡ x + (y + z)
+assoc zero y z = refl
+assoc (suc x) y z = cong suc (+assoc x y z)

{-# COMMASSOC +comm #-}

data Singleton : Nat → Set where
    just : (n : Nat) → Singleton n

-- end of thesis stuff
-- resolving meta variables with injectivity analysis
-- inj1 : (a b : Nat) → Singleton (a + b)
-- inj1 a b = just (_ + b)

-- inj1c : (b : Nat) → Singleton (suc b)
-- inj1c b = just (_ + b)

-- ????????????
inj1d : (b : Nat) → Singleton (b)
inj1d b = just (_ + b)

inj1v : (a : Nat) → Singleton (suc a)
inj1v a = just (_ + 1)

-- inj2 : (a b : Nat) → Singleton (a + b)
-- inj2 a b = just (a + _)

-- inj2c : (a : Nat) → Singleton (suc a)
-- inj2c a = just (a + _)

inj2v : (b : Nat) → Singleton (suc b)
inj2v b = just (1 + _)


infixr 20 _⊓_
_⊓_ : Nat → Nat → Nat
zero ⊓ y = zero
x ⊓ zero = zero
suc x ⊓ suc y = suc (x ⊓ y)

min-zero : (m : Nat) → m ⊓ zero ≡ zero
min-zero zero = refl
min-zero (suc m) = refl

{-# REWRITE min-zero #-}

inj-min : (a b : Nat) → Singleton (suc (a ⊓ b))
inj-min a b = just (_ ⊓ _)

inj-min2 : (a b : Nat) → Singleton (zero)
inj-min2 a b = just (a ⊓ _)

inj-min3 : (a b : Nat) → Singleton (zero)
inj-min3 a b = just (_ ⊓ b)

-- inj-min4 : (a b : Nat) → Singleton (zero)
-- inj-min4 a b = just (_ ⊓ zero)


-- dist-d : (x y d : Nat) → d + (x ⊓ y) ≡ (d + x) ⊓ (d + y)
-- dist-d x y zero = refl
-- dist-d x y (suc d) = cong suc (dist-d x y d)

-- {-# REWRITE dist-d #-}

-- min-x-d : (x d : Nat) → (d + x) ⊓ x ≡ x
-- min-x-d zero d = refl
-- min-x-d (suc x) d = cong suc (min-x-d x d)

min-comm : (m n : Nat) → m ⊓ n ≡ n ⊓ m
min-comm zero n = refl
min-comm (suc m) zero = refl
min-comm (suc m) (suc n) rewrite min-comm m n = refl

-- -- TODO: prove associative

{-# COMMASSOC min-comm #-}

min-test : (m n o : Nat) → suc m ⊓ n ⊓ suc o ≡ n ⊓ suc (m ⊓ o)
min-test m n o = refl

-- open import Agda.Primitive

-- -- Set consumes an argument maybe?
-- weird : Set (lsuc lzero)
-- weird = Set

-- weird2 : zero
-- weird2 = ?

-- Bool2 : Set lzero
-- Bool2 = (A : Set lzero) → A → A → A


-- VEC SWAP

data Vec (A : Set) : Nat → Set where
    [] : Vec A zero
    _∷_ : ∀ (x : A) {n : Nat} (xs : Vec A n) → Vec A (suc n) 

infixr 5 _∷_

take : ∀ {A} (p : Nat) {o} → Vec A (p + o) → Vec A p
take zero xs = []
take (suc n) {o} (x ∷ xs) = x ∷ take n {o} xs

skip : ∀ {A} (p : Nat) {o} → Vec A (p + o) → Vec A o
skip zero xs = xs
skip (suc n) (x ∷ xs) = skip n xs

-- _++_ : ∀ {A} {p o : Nat} → Vec A p → Vec A o → Vec A (p + o)
-- _++_ [] ys = ys
-- _++_ (x ∷ xs) ys = x ∷ (xs ++ ys)

-- infixr 4 _++_

-- swap : ∀ {A} (p : Nat) {o} → Vec A (p + o) → Vec A (p + o)
-- swap p {o} xs = skip p {o} xs ++ take p {o} xs 

-- swap_test1 : Vec Nat 4
-- swap_test1 = swap 2 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])

-- swap_test2 : Vec Nat 5
-- swap_test2 = swap 3 (1 ∷ [] ++ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])


-- data Weird : Set where
--     N0 : Weird
--     N1 : Weird
--     N2 : Weird

-- _⊕_ : Weird → Weird → Weird
-- N0 ⊕ y = y
-- x ⊕ N0 = x
-- N1 ⊕ N1 = N2
-- x ⊕ N2 = N2
-- N2 ⊕ y = N2

-- assoc : (x y z : Weird) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
-- assoc N0 y z = refl
-- assoc N1 N0 z = refl
-- assoc N1 N1 N0 = refl
-- assoc N1 N1 N1 = refl
-- assoc N1 N1 N2 = refl
-- assoc N1 N2 N0 = refl
-- assoc N1 N2 N1 = refl
-- assoc N1 N2 N2 = refl
-- assoc N2 N0 z = refl
-- assoc N2 N1 N0 = refl
-- assoc N2 N1 N1 = refl
-- assoc N2 N1 N2 = refl
-- assoc N2 N2 N0 = refl
-- assoc N2 N2 N1 = refl
-- assoc N2 N2 N2 = refl 

