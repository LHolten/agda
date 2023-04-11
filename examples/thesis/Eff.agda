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
-- open import Agda.Builtin.Cubical.Path

get-eff : Nat → Set
get-eff 0 = List Bool
get-eff 1 = List Nat
get-eff _ = ⊤

record Monoid (A : Set) : Set₁ where
  field
    mempty : A
    _<>_   : A → A → A
    index : Σ Nat λ n → get-eff n ≡ A
open Monoid {{...}}

infixl 20 _&&_
_&&_ : Bool → Bool → Bool
true && x = x
false && _ = false
-- x && true = x
-- _ && false = false

postulate
    -- _∈_ : Set → List Nat → bool
    -- l-Ø : (xs : Eff []) → Ø && xs ≡ xs
    -- r-Ø : (xs : Eff []) → xs && Ø ≡ xs
    x&&true : ∀ {x} → x && true ≡ x
    &&false : ∀ {x} → x && false ≡ false
    &&-comm : ∀ (xs ys : Bool) → xs && ys ≡ ys && xs
    &&-assoc : ∀ (xs ys zs : Bool) → (xs && ys) && zs ≡ xs && (ys && zs)

{-# REWRITE x&&true &&false #-}
{-# COMMASSOC &&-comm #-}


_++_ : {A : Set} → List A → List A → List A
[] ++ r = r
(x ∷ l) ++ r = x ∷ (l ++ r)

xs++[] : ∀ {A} (xs : List A) → xs ++ [] ≡ xs
xs++[] [] = refl
xs++[] (x ∷ xs) = cong (_∷_ x) (xs++[] xs)

{-# REWRITE xs++[] #-}


data WithEff : ∀ {L : List Nat} (v : Bool) (O : Set) → Set₁ where
    pure : ∀ {v O} → O → WithEff {[]} v O
    emit : ∀ {L E v} → get-eff E → WithEff {E ∷ L} v ⊤
    inc : ∀ {L E v O} → WithEff {L} v O → WithEff {E ∷ L} v O
    _>>=_ : ∀ {L v X O} → WithEff {L} v X → (X → WithEff {L} v O) → WithEff {L} v O
    fail : ∀ {L O} → WithEff {L} false O

_>>_ : ∀ {L v O} → WithEff {L} v ⊤ → WithEff {L} v O → WithEff {L} v O
left >> right = left >>= λ tt → right

raise : ∀ {B v L O} → WithEff {L} true O → WithEff {B ++ L} v O
raise {[]} {false} s = fail
raise {[]} {true} s = s
raise {E ∷ L} {v} s = inc (raise {L} {v} s)

smart-pure : ∀ {B v O} → O → WithEff {B} v O
smart-pure {B} {v} o = raise {B} {v} (pure o)

data Index (x : Nat) : (List Nat) → Set where
    here : ∀ {xs} → Index x (x ∷ xs)
    there : ∀ {y xs} → Index x xs → Index x (y ∷ xs)
    nvm : Index x []

cmp : (x y : Nat) → Maybe (x ≡ y)
cmp zero zero = just refl
cmp zero (suc y) = nothing
cmp (suc x) zero = nothing
cmp (suc x) (suc y) = case (cmp x y) of λ where
    (just refl) → just refl
    nothing → nothing

idx : ∀ x xs → Index x xs
idx y [] = nvm
idx y (x ∷ xs) = case (cmp x y) of λ where
    (just refl) → here
    nothing → there (idx y xs)

eff-idx : ∀ {x xs} → Index x xs → Bool
eff-idx here = true
eff-idx (there i) = eff-idx i
eff-idx nvm = false

eff : ∀ {L : List Nat} (E : Nat) → Bool
eff {xs} E = eff-idx (idx E xs)

emit-idx : ∀ {v x xs} → (i : Index x xs) → get-eff x → WithEff {xs} (v && eff-idx i) ⊤
emit-idx here e = emit e
emit-idx {v} (there i) e = inc (emit-idx {v} i e)
emit-idx nvm e = fail

smart-emit : ∀ {E L v} → get-eff E → WithEff {L} (v && eff {L} E) ⊤
smart-emit {E} {xs} {v} e = emit-idx {v} (idx E xs) e


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
  NatMonoid : Monoid (List Nat)
  mempty {{NatMonoid}} = []
  _<>_   {{NatMonoid}} xs ys = xs ++ ys
  index  {{NatMonoid}} = 1 , refl

instance
  BoolMonoid : Monoid (List Bool)
  mempty {{BoolMonoid}} = []
  _<>_   {{BoolMonoid}} xs ys = xs ++ ys
  index  {{BoolMonoid}} = 0 , refl

test : ∀ {L} → WithEff {L} (eff {L} 0 && eff {L} 1) ⊤
test {L} = do
    smart-emit {1} {_} {eff {L} 0} (10 ∷ [])
    smart-emit {0} {_} {eff {L} 1} (true ∷ [])
    smart-emit {1} {_} {eff {L} 0} (42 ∷ [])

main : List Nat
main = eval do
    (nats , bools) ← handle {0} do
        (tt , nats) ← handle {1} test
        smart-pure nats
    smart-pure nats


main1 : ∀ {L} → WithEff {L} (eff {L} 0) (List Nat)
main1 = do
    (tt , nats) ← handle {1} test
    smart-pure nats

-- -- data Singleton : List Nat → Set₁ where
-- --     just : (n : List Nat) → Singleton n

-- -- test-mix : Singleton (Nat ∷ Bool ∷ [])
-- -- test-mix = just (mix (Nat ∷ []) (Bool ∷ []))

-- -- test : ∀ {ES} → WithEff (mix ES (mix (List Bool ∷ []) (List Nat ∷ []))) ⊤
-- -- test = do
-- --     smart-emit (10 ∷ [])
-- --     smart-emit (true ∷ [])
-- --     smart-emit (42 ∷ [])

-- -- data WithBag : (ES : Eff) (o : Set) → Set₁ where
-- --     pure : ∀ {ES O} → O → WithEff ES O

-- -- lower : ∀ (E ES) → WithBag (bag E && ES) → WithEff (E ∷ ES)


-- -- postulate
-- --     choose : ∀ {e es E ES O} 
-- --         → WithEff (E ∷ ((e ∷ es) && ES)) O
-- --         → WithEff (e ∷ (es && (E ∷ ES))) O
-- --         → WithEff ((e ∷ es) && (E ∷ ES)) O

-- -- raise : ∀ {ES ES' O} → WithEff ES' O → WithEff (ES && ES') O
-- -- raise {Ø} s = s
-- -- raise {e ∷ es} (pure x) = inc (raise (pure x))
-- -- raise {e ∷ es} (emit {E} {ES} x) = choose {e} {es} {E} {ES} (emit x) (inc (raise {es} (emit {E} {ES} x)))
-- -- raise {e ∷ es} (inc {E} {ES} s) = choose {e} {es} {E} {ES} (inc (raise {e ∷ es} s)) (inc (raise {es} (inc {E} {ES} s)))
-- -- raise {es} (s >>= x) = raise {es} s >>= λ r → raise {es} (x r)
    