open import Agda.Builtin.Equality
open import Agda.Builtin.List
-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
cong : ∀ { a b} { A : Set a }  { B : Set b }
       (f : A → B ) {m  n}  → m ≡ n → f m ≡ f n
cong f refl = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y → P x → P y
subst P refl px = px

subst2 : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y → P y → P x
subst2 P refl px = px

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

infix  3 _∎
infixr 2 _≡⟨⟩_ step-≡ step-≡˘
infix  1 begin_

begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

_≡⟨⟩_ : {A : Set} (x {y} : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

step-≡ : {A : Set} (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ y≡z x≡y = trans x≡y y≡z

step-≡˘ : {A : Set} (x {y z} : A) → y ≡ z → y ≡ x → x ≡ z
step-≡˘ _ y≡z y≡x = trans (sym y≡x) y≡z

syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

_∎ : {A : Set} (x : A) → x ≡ x
_∎ _ = refl

data Term (H : Set) : Set where
    var : Term H
    con : H → Term H

infix 20 _⊕_
postulate
    H : Set
    _⊕'_ : H → H → H
    ⊕'-assoc : {u v w : H} → u ⊕' (v ⊕' w) ≡ (u ⊕' v) ⊕' w
    
    _⊕_ : Term H → Term H → Term H
    ⊕-assoc : {u v w : Term H} → u ⊕ (v ⊕ w) ≡ (u ⊕ v) ⊕ w

    var-left : {z x : Term H} {res : H}
      → var ⊕ z ≡ con res
      → x ⊕ z ≡ var ⊕ z
    var-right : {z x : Term H} {res : H}
      → z ⊕ var ≡ con res
      → z ⊕ x ≡ z ⊕ var
    con-con : {x y : H} → con x ⊕ con y ≡ con (x ⊕' y)

var-var : {x y : Term H} {res : H} 
  → var ⊕ var ≡ con res 
  → x ⊕ y ≡ con res
var-var {x} {y} {res} p = let 
    l : var ⊕ y ≡ con res
    l = begin 
        var ⊕ y
      ≡⟨ var-right p ⟩
        p
  in begin
    x ⊕ y
  ≡⟨ var-left l ⟩
    l

r-consume : (x : Term H) (res : H) 
  → x ⊕ var ≡ con res
  → con res ⊕ var ≡ con res
r-consume x res p = begin
    con res ⊕ var
  ≡˘⟨ cong (λ y → y ⊕ var) p ⟩
    (x ⊕ var) ⊕ var 
  ≡˘⟨ ⊕-assoc ⟩
    x ⊕ (var ⊕ var)
  ≡⟨ var-right p ⟩ 
    x ⊕ var
  ≡⟨ p ⟩
    con res
  ∎

l-consume : (x : Term H) (res : H) 
  → var ⊕ x ≡ con res
  → var ⊕ con res ≡ con res
l-consume x res p = begin 
    var ⊕ con res
  ≡˘⟨ cong (_⊕_ var) p ⟩
    var ⊕ (var ⊕ x)
  ≡⟨ ⊕-assoc ⟩ 
    (var ⊕ var) ⊕ x
  ≡⟨ var-left p ⟩ 
    var ⊕ x
  ≡⟨ p ⟩
    con res
  ∎

left-right : (l r : H) 
  → con l ⊕ var ≡ con l
  → var ⊕ con r ≡ con r
  → con l ≡ con r
left-right l r p q = begin
    con l
  ≡˘⟨ p ⟩ 
    con l ⊕ var
  ≡˘⟨ var-right p ⟩ 
    con l ⊕ con r 
  ≡⟨ var-left q ⟩ 
    var ⊕ con r
  ≡⟨ q ⟩
    con r 
  ∎

the : (u v w : Term H) {res1 res2 : H}
    → u ⊕ v ≡ con res1
    → v ⊕ w ≡ con res2
    → u ⊕ (v ⊕ w) ≡ con res1
the var var w p q = var-var p
the var (con x) var {res1} {res2} p q = let 
    l = l-consume (con x) res1 p
    r = r-consume (con x) res2 q
    lr = left-right res2 res1 r l
  in begin
    var ⊕ (con x ⊕ var)
  ≡⟨ cong (_⊕_ var) q ⟩ 
    var ⊕ con res2
  ≡⟨ cong (_⊕_ var) lr ⟩
    var ⊕ con res1
  ≡⟨ l ⟩
    con res1
  ∎
the u v (con x) p q = {!   !}
the (con x) v w p q = {!   !}

-- data W : Set where
--     X : W
--     L : W
--     R : W

-- f : W → W → W
-- f X b = X
-- f a b = {!   !}

-- f-assoc : (a b c : W) → f (f a b) c ≡ f a (f b c)
-- f-assoc X b c = {!   !}
-- f-assoc Y b c = {!   !}

-- postulate
--     H : Set
--     _⊕_ : H → H → H
--     ⊕-assoc : {u v w : H} → (u ⊕ v) ⊕ w ≡ u ⊕ (v ⊕ w)

-- data Term : Set where
--     var : Term
--     con : H → Term

-- data Singleton : H → Set where
--     just : (h : H) → Singleton h

-- -- Rule : Term → Term → Set
-- -- Rule var var = {x y : H} → Singleton (x ⊕ y)
-- -- Rule var (con y) = {x : H} → Singleton (x ⊕ y)
-- -- Rule (con x) var = {y : H} → Singleton (x ⊕ y)
-- -- Rule (con x) (con y) = Singleton (x ⊕ y)

-- Inner : List Term → H → Set
-- Inner [] res = Singleton res
-- Inner (var ∷ terms) res = {x : H} → Inner terms (x ⊕ res)
-- Inner (con x ∷ terms) res = Inner terms (x ⊕ res)

-- Rule : Term → List Term → Set
-- Rule var terms = {x : H} → Inner terms x
-- Rule (con x) terms = Inner terms x

-- Rule2 : Term → Term → Set
-- Rule2 a b = Rule a (b ∷ [])

-- Rule3 : Term → Term → Term → Set
-- Rule3 a b c = Rule a (b ∷ c ∷ [])

-- r-consume : (x : Term) 
--     → Rule2 x var
--     → Rule3 x var var
-- r-consume var p = p
-- r-consume (con x) p = subst Singleton ⊕-assoc p

-- l-consume : (x : Term) 
--     → Rule2 var x
--     → Rule3 var var x
-- l-consume var p = p
-- l-consume (con y) p = p


-- the : (u v w : Term)
--     → Rule2 u v
--     → Rule2 v w
--     → Rule3 u v w
-- the u v w p q = {!   !}

-- Knuth Bendix 

-- suc x = x + _1			=> _1 = suc _2
-- suc x = suc (x + _2)	=> _2 = zero
-- suc x = sux x 