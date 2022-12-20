{-# OPTIONS --rewriting --no-fast-reduce #-}

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

+assoc : m + (n + o) ≡ m + n + o
+assoc {m = zero} = refl
+assoc {m = suc m} = cong suc (+assoc {m})

{-# REWRITE +zero +suc +assoc #-}

-- test : ( m + m + 1 + n + 1 ≡ 2 + (n + m) + m )
-- test = refl

-- test2 : m + (n + o) ≡ (m + n) + o
-- test2 = refl

test2 : m + n ≡ n + m
test2 = {!   !}

{-# COMMASSOC #-}

test3 : m + n ≡ n + m
test3 = {!   !}

test4 : 2 + o + n + m ≡ o + m + n + 2
test4 = {!   !}

test5 : zero ≡ n + 2 + (m + m) + n
test5 = {!   !}