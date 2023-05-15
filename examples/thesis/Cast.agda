{-# OPTIONS --rewriting --no-fast-reduce #-}

open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import PlusComm1

-- data Vec (A : Set) : Nat → Set where

-- cong : ∀ {l m} {A : Set l} {B : Set m} (P : A → B) {x y : A} → x ≡ y → P x ≡ P y
-- cong _ refl = refl

x+0≡x : (x : Nat) → x + 0 ≡ x
x+0≡x zero = refl
x+0≡x (suc x) = cong suc (x+0≡x x) 

-- cast : {A B : Set} → A ≡ B → A → B
-- cast refl x = x

-- cast-vec : {A : Set} {x : Nat} → Vec A (x + 0) → Vec A x
-- cast-vec {A} {x} v = cast (cong (Vec A) (x+0≡x x)) v

cast : ∀ {l m} {A : Set l} (P : A → Set m) 
    {x y : A} → x ≡ y → P x → P y
cast _ refl x = x

cast-vec : {A : Set} {x : Nat} → Vec A (x + 0) → Vec A x
cast-vec {A} {x} v = cast (Vec A) (x+0≡x x) v

-- for l ↪ r if Γ ⊢ σ l : T, then Γ ⊢ σ r : T