{-# OPTIONS --rewriting --no-fast-reduce --local-confluence-check #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Unit

cong : ∀ {A B : Set} (f : A → B) {m n} → m ≡ n → f m ≡ f n
cong f refl = refl

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

infixr 20 _⊓_
_⊓_ : Nat → Nat → Nat
zero ⊓ y = zero
x ⊓ zero = zero
suc x ⊓ suc y = suc (x ⊓ y)

min-zero : (m : Nat) → m ⊓ zero ≡ zero
min-zero zero = refl
min-zero (suc m) = refl

{-# REWRITE min-zero #-}

min-assoc : (a b c : Nat) → (a ⊓ b) ⊓ c ≡ a ⊓ (b ⊓ c)
min-assoc zero b c = refl
min-assoc a zero c = refl
min-assoc a b zero = refl
min-assoc (suc a) (suc b) (suc c) = cong suc (min-assoc a b c)

min-suc-suc : (a b c : Nat) → suc a ⊓ (suc b ⊓ c) ≡ suc (a ⊓ b) ⊓ c
min-suc-suc a b zero = refl
min-suc-suc a b (suc c) = cong suc (sym (min-assoc a b c))

{-# REWRITE min-assoc min-suc-suc #-}

data T : Set where
    A : T
    B : T

postulate
    f : T → T → T
    f-ab : f A B ≡ B
    f-assoc : (x y z : T) → f (f x y) z ≡ f x (f y z)
    {-# REWRITE f-ab f-assoc #-}