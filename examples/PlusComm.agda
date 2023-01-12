{-# OPTIONS --rewriting --no-fast-reduce #-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

variable
    m n o : Nat

cong : ∀ { a b} { A : Set a }  { B : Set b }
       (f : A → B ) {m  n}  → m ≡ n → f m ≡ f n
cong f refl = refl

+zero : m + zero ≡ m
+zero {m = zero}  = refl
+zero {m = suc m} = cong suc +zero

+suc : m + (suc n) ≡ suc (m + n)
+suc {m = zero}  = refl
+suc {m = suc m} = cong suc +suc

-- +assoc : m + (n + o) ≡ m + n + o
-- +assoc {m = zero} = refl
-- +assoc {m = suc m} = cong suc (+assoc {m})

{-# REWRITE +zero +suc #-}
{-# COMMASSOC _+_ #-}

test : ( m + m + 1 + n + 1 ≡ 2 + (n + m) + m )
test = refl

test2 : m + (n + o) ≡ (m + n) + o
test2 = refl

test3 : m + n ≡ n + m
test3 = refl

test4 : 2 + o + n + m ≡ o + m + n + 2
test4 = refl

data Bag : Set where
    [_] : Nat → Bag
    _++_ : Bag → Bag → Bag

pattern [_,_] y z = [ y ] ++ [ z ]
pattern [_,_,_] x y z = [ x , y ] ++ [ z ]
pattern [_,_,_,_] w x y z = [ w , x , y ] ++ [ z ]
pattern [_,_,_,_,_] v w x y z = [ v , w , x , y ] ++ [ z ]
pattern [_,_,_,_,_,_] u v w x y z = [ u , v , w , x , y ] ++ [ z ]

infixl 20 _++_

{-# COMMASSOC _++_ #-}

test-comm : [ o ] ++ [ m , n ] ≡ [ o , m ] ++ [ n ]
test-comm = refl

data _∈_ : Nat → Bag → Set where
    proof : ∀ {xs} {x} → x ∈ [ x ] ++ xs
infix 19 _∈_

test-member : ∀ {o n m} → m ∈ [ o , m , n ]
test-member {o} {n} = proof {[ o , n ]}

data _⊆_ : Bag → Bag → Set where
    proof : ∀ {ys} {xs} → xs ⊆ xs ++ ys
infix 19 _⊆_

test-subseteq : ∀ {m o n} → [ o , n ] ⊆ [ o , m , n ]
test-subseteq {m} = proof {[ m ]}


-- sum of types
data _⊕_ : Set → Set → Set where
    inj : ∀ (B : Set) {A} → A → A ⊕ B
infixl 20 _⊕_

{-# COMMASSOC _⊕_ #-}

zero-to-tt : Nat → Nat ⊕ ⊤
zero-to-tt zero = inj Nat tt
zero-to-tt (suc n) = inj ⊤ (suc n)