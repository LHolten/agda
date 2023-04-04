{-# OPTIONS --rewriting --no-fast-reduce #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite



-- postulate
--     instance
--         ListMonoid : ∀ {a} {A : Set a} → Monoid (List A)

--     Eff : Set₁
--     Ø : Eff
--     eff : Set → Eff
--     _++_ : Eff → Eff → Eff
--     l-Ø : (xs : Eff) → Ø ++ xs ≡ xs
--     r-Ø : (xs : Eff) → xs ++ Ø ≡ xs
--     ++-comm : (xs ys : Eff) → xs ++ ys ≡ ys ++ xs
--     ++-assoc : (xs ys zs : Eff) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

-- {-# COMMASSOC ++-comm #-}
-- {-# REWRITE l-Ø r-Ø #-}

-- postulate
--     Emit : Eff → Set₁
--     emit-just : {E : Set} {ES : Eff} → E → Emit (eff E ++ ES)
    
--     emit-elim : ∀ {l} (P : (ES : Eff) → Set l)
--               → (f : {E : Set} → (ES : Eff) → E → P (eff E ++ ES) )
--               → {ES : Eff} → Emit ES → P ES

--     emit-elim-rewr : ∀ {l} (P : (ES : Eff) → Set l)
--               → (f : {E : Set} → (ES : Eff) → E → P (eff E ++ ES) )
--               → {E : Set} {ES : Eff} {e : E} 
--               → emit-elim P f {eff E ++ ES} (emit-just {E} {ES} e) ≡ f {E} ES e

record Monoid {a} (A : Set a) : Set a where
  field
    mempty : A
    _<>_   : A → A → A
open Monoid {{...}}

postulate
    instance
        ListMonoid : ∀ {a} {A : Set a} → Monoid (List A)


data Index : List Set → Set → Set where
    zero : ∀ {T ES} → Index (T ∷ ES) T
    suc : ∀ {E ES T} → {{Index ES T}} → Index (E ∷ ES) T

instance 
    zero-idx : ∀ {T ES} → Index (T ∷ ES) T
    zero-idx = zero


data WithEff (f : List Set) : (O : Set) → Set₁ where
    pure : ∀ {O} → O → WithEff f O
    emit : ∀ {E} → {{Index f E}} → E → WithEff f ⊤
    _>>_ : ∀ {O} → WithEff f ⊤ → WithEff f O → WithEff f O
    _>>=_ : ∀ {X O} → WithEff f X → (X → WithEff f O) → WithEff f O

record Handle (O E : Set) : Set where
    constructor _,_
    field
        res : O
        eff : E

handle : ∀ {E ES O} → WithEff (E ∷ ES) O → {{Monoid E}} → WithEff ES (Handle O E)
handle (pure o) = pure (o , mempty)
handle (emit ⦃ zero ⦄ e) = pure (tt , e)
handle (emit ⦃ suc ⦄ e) = do
    emit e
    pure (tt , mempty)
handle (left >> right) = do
    (tt , e1) ← handle left
    (r , e2) ← handle right
    pure (r , (e1 <> e2)) 
handle (left >>= right) = do
    (l , e1) ← handle left
    (r , e2) ← handle (right l)
    pure (r , (e1 <> e2))

eval : ∀ {O} → WithEff [] O → O
eval (pure x) = x
eval (left >> right) = eval right
eval (left >>= right) = eval (right (eval left))


test : ∀ {f} → {{Index f (List Nat)}} → {{Index f (List Bool)}} → WithEff f ⊤
test = do
    emit (10 ∷ [])
    emit (true ∷ [])
    emit (42 ∷ [])

main : List Nat
main = eval do
    (bools , nats) ← handle do
        (tt , bools) ← handle test
        pure bools
    pure nats



-- data WithEff : Eff → Set → Set₁ where
--     pure : ∀ {ES O} → O → WithEff ES O
--     -- emit : ∀ {E ES} → E → WithEff (eff E ++ ES) ⊤
--     emit : ∀ {ES} → Emit ES → WithEff ES ⊤
--     _>>_ : ∀ {ES O} → WithEff ES ⊤ → WithEff ES O → WithEff ES O

-- handle : ∀ {E ES} → WithEff (eff E ++ ES) ⊤ → {{Monoid E}} → WithEff ES E
-- handle (pure o) = pure mempty
-- handle {E} {ES} (emit e) = emit-elim (λ _ → WithEff ES E) (λ 
--     { {E} _ e → {!   !}
--     ; {_} _ o → {!   !} 
--     }) e
-- handle _ = {!   !}

-- data IO : Set where
--     print : Nat → IO

-- test : WithEff (eff IO) ⊤
-- test = do
--     emit (emit-just (print 10))
--     emit (emit-just (print 42))
