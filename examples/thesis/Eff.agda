{-# OPTIONS --rewriting --no-fast-reduce #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma
open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Reflection
open import PlusComm1
open import Cast
-- open import Agda.Builtin.Cubical.Path

data Eff : Set where
    Bools : Eff
    Nats : Eff

get-eff : Eff → Set
get-eff Bools = List Bool
get-eff Nats = List Nat

cmp : (x y : Eff) → Maybe (x ≡ y)
cmp Nats Nats = just refl
cmp Bools Bools = just refl
cmp _ _ = nothing

record Monoid (A : Set) : Set where
  field
    mempty : A
    _<>_   : A → A → A
open Monoid {{...}}

infixl 20 _&&'_
_&&'_ : Bool → Bool → Bool
true &&' x = x
false &&' _ = false

x&&'true : ∀ x → x &&' true ≡ x
x&&'true false = refl
x&&'true true = refl

&&'false : ∀ x → x &&' false ≡ false
&&'false false = refl
&&'false true = refl

x&&'x : ∀ x → x &&' x ≡ x
x&&'x false = refl
x&&'x true = refl

{-# REWRITE x&&'true &&'false x&&'x #-}

&&'-comm : ∀ (x y : Bool) → x &&' y ≡ y &&' x
&&'-comm false y = refl
&&'-comm true y = refl

&&'-assoc : ∀ (x y z : Bool) → (x &&' y) &&' z ≡ x &&' (y &&' z)
&&'-assoc false y z = refl
&&'-assoc x false z = refl
&&'-assoc x y false = refl
&&'-assoc true true true = refl

{-# COMMASSOC &&'-comm #-}

Cond : Set
Cond = List Eff → Bool

infixl 20 _&&_
_&&_ : Cond → Cond → Cond
p && q = λ x → (p x) &&' (q x)

_++_ : {A : Set} → List A → List A → List A
[] ++ r = r
(x ∷ l) ++ r = x ∷ (l ++ r)

xs++[] : ∀ {A} (xs : List A) → xs ++ [] ≡ xs
xs++[] [] = refl
xs++[] (x ∷ xs) = cong (_∷_ x) (xs++[] xs)

{-# REWRITE xs++[] #-}


data WithEff : ∀ {L : List Eff} (v : Bool) (O : Set) → Set₁ where
    pure : ∀ {v O} → O → WithEff {[]} v O
    emit : ∀ {L E v} → get-eff E → WithEff {E ∷ L} v ⊤
    inc : ∀ {L E v O} → WithEff {L} v O → WithEff {E ∷ L} v O
    _>>=_ : ∀ {L v X O} → WithEff {L} v X → (X → WithEff {L} v O) → WithEff {L} v O
    fail : ∀ {L O} → WithEff {L} false O

_>>_ : ∀ {L v O} → WithEff {L} v ⊤ → WithEff {L} v O → WithEff {L} v O
left >> right = left >>= λ tt → right

WithEff' : (c : Cond) (O : Set) → Set₁
WithEff' c O = {xs : List Eff} → WithEff {xs} (c xs) O

raise : ∀ {B v L O} → WithEff {L} true O → WithEff {B ++ L} v O
raise {[]} {false} s = fail
raise {[]} {true} s = s
raise {E ∷ L} {v} s = inc (raise {L} {v} s)

smart-pure : ∀ {B v O} → O → WithEff {B} v O
smart-pure {B} {v} o = raise {B} {v} (pure o)

data Index (x : Eff) : (List Eff) → Set where
    here : ∀ {xs} → Index x (x ∷ xs)
    there : ∀ {y xs} → Index x xs → Index x (y ∷ xs)
    nvm : Index x []

idx : ∀ x xs → Index x xs
idx y [] = nvm
idx y (x ∷ xs) = case (cmp x y) of λ where
    (just refl) → here
    nothing → there (idx y xs)

eff-idx : ∀ {x xs} → Index x xs → Bool
eff-idx here = true
eff-idx (there i) = eff-idx i
eff-idx nvm = false

eff : (E : Eff) → Cond
eff E = λ xs → eff-idx (idx E xs)

emit-idx : {v : Bool} → ∀ {x xs} → (i : Index x xs) → get-eff x → WithEff {xs} (v &&' eff-idx i) ⊤
emit-idx here e = emit e
emit-idx {v} (there i) e = inc (emit-idx {v} i e)
emit-idx nvm e = fail

smart-emit : ∀ {E v xs} → {{v &&' eff E xs ≡ v}} → get-eff E → WithEff {xs} v ⊤
smart-emit {E} {v} {xs} {{p}} e = cast (λ x → WithEff x ⊤) p (emit-idx {v} (idx E xs) e)


data Handle (O E : Set) : Set where
    _,_ : O → E → Handle O E


handle : ∀ {e L O v} → {{f : Monoid (get-eff e)}} → WithEff {e ∷ L} v O → WithEff {L} v (Handle O (get-eff e))
handle fail = fail
handle (emit e) = smart-pure (tt , e)
handle (inc s) = do
    r ← s
    smart-pure (r , mempty)
handle (s1 >>= s2) = do
    (l , e1) ← handle s1
    (r , e2) ← handle (s2 l)
    smart-pure (r , (e1 <> e2))

eval : ∀ {O} → WithEff {[]} true O → O
eval (pure x) = x
eval (s1 >>= s2) = eval (s2 (eval s1))

instance
  ListMonoid : ∀ {A} → Monoid (List A)
  mempty {{ListMonoid}} = []
  _<>_   {{ListMonoid}} xs ys = xs ++ ys

test : WithEff' (eff Nats && eff Bools) ⊤
test = do
    smart-emit {Nats} (10 ∷ [])
    smart-emit {Bools} (true ∷ [])
    smart-emit {Nats} (42 ∷ [])

main : List Nat
main = eval do
    (nats , bools) ← handle {Bools} do
        (tt , nats) ← handle {Nats} test
        smart-pure nats
    smart-pure nats

main1 : WithEff' (eff Bools) (List Nat)
main1 = do
    (tt , nats) ← handle {Nats} test
    smart-pure nats
