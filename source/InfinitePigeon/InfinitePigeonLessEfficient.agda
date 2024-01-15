-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K #-}

module InfinitePigeon.InfinitePigeonLessEfficient where

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

-- 29 April -3rd May 2011.

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

-- This is the first version. Much improved ones are in other files.
-- Also, this proof switches the case analysis, and this causes funny
-- subsequences in some cases.


-- Definition

Pigeonhole-Lemma : {R : Ω} → ₂ℕ → Ω
Pigeonhole-Lemma {R} α =
  ∃ \(b : ₂) → ∃ \(f : ℕ → ℕ) → ∀(n : ℕ) → K{R}(α(n + f n + 1) ≡ b)


pigeonhole-lemma : {R : Ω} →
----------------

 ∀(α : ₂ℕ) → K (Pigeonhole-Lemma α)

pigeonhole-lemma {R} α =  K-∨-elim case₀ case₁ K-Excluded-Middle
 where
  A : Ω
  A = ∀(n : ℕ) → K∃ \(i : ℕ) → K(α(n + i + 1) ≡ ₁)

  case₀ : A → K(Pigeonhole-Lemma α)
  case₀ a = K-functor lemma₂ lemma₁
   where
    lemma₁ : K∃ \(f : ℕ → ℕ) → ∀(n : ℕ) → K(α(n + f n + 1) ≡ ₁)
    lemma₁ = K-AC-ℕ (λ n → λ r → ∃-intro 0 (λ p → r)) a

    lemma₂ : (∃ \(f : ℕ → ℕ) → ∀(n : ℕ) → K(α(n + f n + 1) ≡ ₁)) →
              ∃ \(b : ₂) → ∃ \(f : ℕ → ℕ) → ∀(n : ℕ) → K(α(n + f n + 1) ≡ b)
    lemma₂ = ∃-intro ₁

  case₁ : (A → R) → K(Pigeonhole-Lemma α)
  case₁ p = lemma₇
   where
    lemma₃ :
      K∃ \(n : ℕ) → (∃ \(i : ℕ) → K(α(n + i + 1) ≡ ₁)) → R
    lemma₃ = not-forall-not-implies-K-exists p

    lemma₄-₁ :
     (∃ \(n : ℕ) → (∃ \(i : ℕ) →  K(α(n + i + 1) ≡ ₁)) → R) →
      ∃ \(n : ℕ) →  ∀  (i : ℕ) → (K(α(n + i + 1) ≡ ₁)) → R
    lemma₄-₁ (∃-intro n e) = ∃-intro n (not-exists-implies-forall-not e)

    lemma₄ :
      K∃ \(n : ℕ) → ∀(i : ℕ) → (K(α(n + i + 1) ≡ ₁)) → R
    lemma₄ = K-functor lemma₄-₁ lemma₃

    lemma₅-₁ :
     (∃ \(n : ℕ) → ∀ (i : ℕ) → K(α(n + i + 1) ≡ ₁ → R)) →
      ∃ \(n : ℕ) → ∀ (i : ℕ) → K(α(n + i + 1) ≡ ₀)
    lemma₅-₁ (∃-intro n f) =
             ∃-intro n (λ i → not-1-must-be-0 (α(n + i + 1)) (f i))

    lemma₅ :
      K∃ \(n : ℕ) → ∀(i : ℕ) → K(α(n + i + 1) ≡ ₀)
    lemma₅ = K-functor lemma₅-₁ lemma₄

    lemma₆-₁ :
     (∃ \(n : ℕ) → ∀(i : ℕ) → K(α(n + i + 1) ≡ ₀)) →
      ∃ \(n : ℕ) → ∀(i : ℕ) → K(α(i + n + 1) ≡ ₀)
    lemma₆-₁ (∃-intro n h) = ∃-intro n (λ i → K-functor(lemma₆-₁-₁ i)(h i))
      where
       lemma₆-₁-₁ : ∀(i : ℕ) → α(n + i + 1) ≡ ₀ → α(i + n + 1) ≡ ₀
       lemma₆-₁-₁ i r = two-things-equal-to-a-third-are-equal lemma₆-₁-₁-₁ r
         where
          lemma₆-₁-₁-₁ : α(n + i + 1) ≡ α(i + n + 1)
          lemma₆-₁-₁-₁ =
            compositionality (λ k → α(k + 1)) (addition-commutativity n i)

    lemma₆ :
      K∃ \(i : ℕ) → ∀(n : ℕ) → K(α(n + i + 1) ≡ ₀)
    lemma₆ = K-functor lemma₆-₁ lemma₅

    lemma₇-₁ :
     (∃ \(i : ℕ) → ∀(n : ℕ) → K(α(n + i + 1) ≡ ₀)) →
      ∃ \(b : ₂) → ∃ \(f : ℕ → ℕ) → ∀(n : ℕ) → K{R}(α(n + f n + 1) ≡ b)
    lemma₇-₁ (∃-intro i a) = ∃-intro ₀ (∃-intro (λ n → i) a)

    lemma₇ : K(Pigeonhole-Lemma α)
    lemma₇ = K-functor lemma₇-₁ lemma₆


-- Definition

Pigeonhole : {R : Ω} → ₂ℕ → Ω
Pigeonhole {R} α =
   ∃ \(b : ₂) → ∃ \(g : ℕ → ℕ) →
   ∀(i : ℕ) → g i < g(i + 1) ∧ K {R} (α(g i) ≡ b)


pigeonhole : {R : Ω} →
----------

 ∀(α : ₂ℕ) → K(Pigeonhole α)

pigeonhole {R} α = K-functor lemma₀ (pigeonhole-lemma {R} α)
 where
  lemma₀ :
    (∃ \(b : ₂) → ∃ \(f : ℕ → ℕ) → ∀(n : ℕ) → K(α(n + f n + 1) ≡ b)) →
     ∃ \(b : ₂) → ∃ \(g : ℕ → ℕ) → ∀(n : ℕ) → g n < g(n + 1) ∧ K {R}(α(g n) ≡ b)
  lemma₀ (∃-intro b (∃-intro f h)) =
          ∃-intro b (∃-intro g λ n → ∧-intro (lemma₁ n) (lemma₂ n))
   where g : ℕ → ℕ
         g 0 = 0 + f 0 + 1
         g(succ n) = let m = g n in m + f m + 1

         lemma₁ : ∀(n : ℕ) → g n < g(n + 1)
         lemma₁ n = less-proof(f(g n))

         lemma₂ : ∀(n : ℕ) → K(α(g n) ≡ b)
         lemma₂ 0 = h 0
         lemma₂ (succ n) = h(g n)
