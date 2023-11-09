-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --safe --without-K #-}

module InfinitePigeon.Naturals where

open import InfinitePigeon.Logic

open import MLTT.Natural-Numbers-Type public renaming (zero to O)

induction : {A : ℕ → Ω} →
---------
            A 0 → (∀(k : ℕ) → A k → A(succ k)) → ∀(n : ℕ) → A n

induction base step 0 = base
induction base step (succ n) = step n (induction base step n)


head : {A : ℕ → Ω} →
----
       (∀(n : ℕ) → A n) → A 0

head α = α 0


tail : {A : ℕ → Ω} →
----
       (∀(n : ℕ) → A n) → ∀(n : ℕ) → A(succ n)

tail α n = α(succ n)


cons : {A : ℕ → Ω} →
----
       A 0 ∧ (∀(n : ℕ) → A(succ n)) → ∀(n : ℕ) → A n

cons (∧-intro a α) 0 = a
cons (∧-intro a α) (succ n) = α n


prefix : {R : Ω} {A : ℕ → Ω} →
------
          A 0 → ((∀(n : ℕ) → A n) → R) → (∀(n : ℕ) → A(succ n)) → R


prefix α₀ p α' = p(cons (∧-intro α₀ α'))


eq-cases : {X : ℕ → Set} → (i j : ℕ) → X i → X j → X j
eq-cases 0 0 x y = x
eq-cases 0 (succ j) x y = y
eq-cases (succ i) 0 x y = y
eq-cases {X} (succ i) (succ j) x y = eq-cases {λ n → X(succ n)} i j x y


mapsto : {X : ℕ → Set} →
  (i : ℕ) → X i → ((j : ℕ) → X j) → (j : ℕ) → X j
mapsto {X} i x α j = eq-cases {X} i j x (α j)
