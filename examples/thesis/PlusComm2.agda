{-# OPTIONS --rewriting --no-fast-reduce #-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

variable
    m n o : Nat

data Bag : Set where
    [_] : Nat → Bag
    _++_ : Bag → Bag → Bag

pattern [_,_] y z = [ y ] ++ [ z ]
pattern [_,_,_] x y z = [ x , y ] ++ [ z ]
pattern [_,_,_,_] w x y z = [ w , x , y ] ++ [ z ]
pattern [_,_,_,_,_] v w x y z = [ v , w , x , y ] ++ [ z ]
pattern [_,_,_,_,_,_] u v w x y z = [ u , v , w , x , y ] ++ [ z ]

infixl 20 _++_

{-# COMMASSOC _++_  #-}

mybag = [ 0 , 1 ]

mybag2 = [ 1 , 0 ]

get : Bag → Nat
get [ x ] = x
get (xs ++ ys) = get xs

get-0 : get mybag ≡ 0
get-0 = refl

get-1 : get mybag2 ≡ 1
get-1 = refl

mybags-equal : mybag ≡ mybag2
mybags-equal = refl

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

data ⊥ : Set where

boom : ⊥ ⊕ ⊤ → ⊥
boom (inj _ p) = p

ohno : ⊥
ohno = boom (inj ⊥ tt)

postulate
    elim : (P : A ⊕ B → Set) 
         → (f : (x : A) → P (inj B x)) 
         → (g : (y : B) → P (inj A y))
         → ((pf : A ≡ B) → (x : A) → f (inj B x) ≡ f (inj A (cast pf x)))
         → (z : A ⊕ B) → P z 

    -- 
    -- elim (λ _ → Nat) (λ x → 0) (λ x → 1) (inj Nat 42)

    elim-inj₁ : elim P f g (inj B x) ≡ f 