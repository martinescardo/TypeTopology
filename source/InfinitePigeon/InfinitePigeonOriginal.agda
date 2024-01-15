-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K #-}

module InfinitePigeon.InfinitePigeonOriginal where

open import InfinitePigeon.Addition
open import InfinitePigeon.Cantor
open import InfinitePigeon.Equality
open import InfinitePigeon.JK-LogicalFacts
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.K-AC-N
open import InfinitePigeon.Logic
open import InfinitePigeon.LogicalFacts
open import InfinitePigeon.Naturals
open import InfinitePigeon.Order
open import InfinitePigeon.Two

-- 6th May 2011.

-- We prove a theorem that involves the classical existential
-- quantifier K∃ (called pigeonhole below). The proof uses excluded
-- middle and classical countable choice (i.e. choice formulated with
-- the classical existential quantifier), which is implemented using
-- the K-shift (more commonly known as the double negation shift) in
-- the modules JK-Choice.agda and Infinite-JK-Shifts.agda.
--
-- In the module FinitePigeon.agda we derive a statement that uses the
-- intuitionistic quantifiers (and doesn't mention the double negation
-- modality K at all), using the classical result as a lemma. In the
-- module Examples.agda we run it.


-- Definition:

Pigeonhole : {R : Ω} → ₂ℕ → Ω
Pigeonhole {R} α =
  ∃ \(b : ₂) → ∃ \(g : ℕ → ℕ) →
  ∀(i : ℕ) → g i < g(i + 1) ∧ K {R} (α(g i) ≡ b)

-- Theorem:

pigeonhole : {R : Ω} →
----------

    ∀(α : ₂ℕ) → K(Pigeonhole α)

pigeonhole {R} α = K-∨-elim case₀ case₁ K-Excluded-Middle
 where
  A : Ω
  A = K∃ \(n : ℕ) → ∀(i : ℕ) → K(α(n + i + 1) ≡ ₀)

  case₀ : A → K(Pigeonhole α)
  case₀ a = K-functor lemma₁ a
   where
    lemma₁ : (∃ \(n : ℕ) → ∀(i : ℕ) → K(α(n + i + 1) ≡ ₀)) → Pigeonhole α
    lemma₁ (∃-intro n h) =
            ∃-intro ₀ (∃-intro (λ i → n + i + 1)
                                λ i → (∧-intro (less-proof 0) (h i)))

  case₁ : (A → R) → K(Pigeonhole α)
  case₁ assumption =  K-functor lemma₇ lemma₆
   where
    lemma₂ : ∀(n : ℕ) → (∀(i : ℕ) → K(α(n + i + 1) ≡ ₀)) → R
    lemma₂ = not-exists-implies-forall-not(three-negations-imply-one assumption)

    lemma₃ : ∀(n : ℕ) → K∃ \(i : ℕ) → K(α(n + i + 1) ≡ ₁)
    lemma₃ = lemma₄ lemma₂
     where
      lemma₄ : (∀(n : ℕ) → (∀(i : ℕ) → K(α(n + i + 1) ≡ ₀)) → R) →
               (∀(n : ℕ) → K∃ \(i : ℕ) → K(α(n + i + 1) ≡ ₁))
      lemma₄ h n = K-functor lemma₅ (not-forall-not-implies-K-exists(h n))
       where
        lemma₅ : (∃ \(i : ℕ) → α(n + i + 1) ≡ ₀ → R) → ∃ \(i : ℕ) → K(α(n + i + 1) ≡ ₁)
        lemma₅ (∃-intro i r) = (∃-intro i (two-equality-cases (α(n + i + 1)) r))

    lemma₆ : K∃ \(f : ℕ → ℕ) → ∀(n : ℕ) → K(α(n + f n + 1) ≡ ₁)
    lemma₆ = K-AC-ℕ (λ n → λ r → ∃-intro 0 (λ p → r)) lemma₃

    lemma₇ : (∃ \(f : ℕ → ℕ) → ∀(n : ℕ) → K(α(n + f n + 1) ≡ ₁)) → Pigeonhole α
    lemma₇ (∃-intro f h) =
            ∃-intro ₁ (∃-intro g λ i → (∧-intro (less-proof (f(g i))) (fact i)))
     where g : ℕ → ℕ
           g 0 = 0 + f 0 + 1
           g(succ n) = let m = g n in  m + f m + 1

           fact : ∀(n : ℕ) → K(α(g n) ≡ ₁)
           fact 0 = h 0
           fact (succ n) = h(g n)
