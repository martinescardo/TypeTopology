-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K #-}

module InfinitePigeon.J-InfinitePigeon where

-- 20 May 2011
--
-- We use the J-translation instead, also called Peirce translation.
--
-- We prefix equations with K.  This eliminates efq R->A for all
-- formulas in the image of the translation.
--
-- We prefix ∃ and ∨ with J.  This eliminates Peirces law JA->A for
-- all formulas in the image of the translation.
--
-- In the end there is not much difference with InfinitePigeon.

open import InfinitePigeon.Addition
open import InfinitePigeon.Cantor
open import InfinitePigeon.Equality
open import InfinitePigeon.J-AC-N
open import InfinitePigeon.JK-LogicalFacts
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.Logic
open import InfinitePigeon.LogicalFacts
open import InfinitePigeon.Naturals
open import InfinitePigeon.Order
open import InfinitePigeon.Two

Pigeonhole : {R : Ω} → ₂ℕ → Ω
Pigeonhole {R} α =
   ∃ \(b : ₂) → ∃ \(g : ℕ → ℕ) →
   ∀(i : ℕ) → g i < g(i + 1) ∧ K {R} (α(g i) ≡ b)


pigeonhole : {R : Ω} →
----------

    ∀(α : ₂ℕ) → J(Pigeonhole α)

pigeonhole {R} α = J-∨-elim case₀ case₁ J-Excluded-Middle
 where
  A : Ω
  A = ∃ \(n : ℕ) → ∀(i : ℕ) → K(α(n + i) ≡ ₀)

  case₀ : A → J(Pigeonhole α)
  case₀ = ηJ ∘ lemma₁
   where
    lemma₁ : A → Pigeonhole α
    lemma₁ (∃-intro n h) =
            ∃-intro ₀ (∃-intro (λ i → n + i)
                                λ i → (∧-intro (less-proof 0) (h i)))

  case₁ : (A → R) → J(Pigeonhole α)
  case₁ assumption =  J-functor lemma₇ lemma₆
   where
    lemma₂ : ∀(n : ℕ) → (∀(i : ℕ) → K(α(n + i) ≡ ₀)) → R
    lemma₂ = not-exists-implies-forall-not assumption

    lemma₃ : ∀(n : ℕ) → J∃ \(i : ℕ) → K(α(n + i) ≡ ₁)
    lemma₃ = lemma₄ lemma₂
     where
      lemma₄ : (∀(n : ℕ) → (∀(i : ℕ) → K(α(n + i) ≡ ₀)) → R) →
               (∀(n : ℕ) → J∃ \(i : ℕ) → K(α(n + i) ≡ ₁))
      lemma₄ h n = K-J {R} efq (K-functor lemma₅ (not-forall-not-implies-K-exists(h n)))
       where
        efq : R → ∃ \(i : ℕ) → K{R}(α(n + i) ≡ ₁)
        efq r = ∃-intro 0 (λ p → r)

        lemma₅ : (∃ \(i : ℕ) → α(n + i) ≡ ₀ → R) → ∃ \(i : ℕ) → K(α(n + i) ≡ ₁)
        lemma₅ (∃-intro i r) = (∃-intro i (two-equality-cases (α(n + i)) r))

    lemma₆ : J∃ \(f : ℕ → ℕ) → ∀(n : ℕ) → K(α(n + f n) ≡ ₁)
    lemma₆ = J-AC-ℕ lemma₃

    lemma₇ : (∃ \(f : ℕ → ℕ) → ∀(n : ℕ) → K(α(n + f n) ≡ ₁)) → Pigeonhole α
    lemma₇ (∃-intro f h) =
            ∃-intro ₁ (∃-intro g λ i → (∧-intro (fact₀ i) (fact₁ i)))
     where
      g : ℕ → ℕ
      g 0 = 0 + f 0
      g(succ i) = let j = g i + 1 in  j + f j

      fact₀ : ∀(i : ℕ) → g i < g(i + 1)
      fact₀ i = let n = f(g i + 1)
                in ∃-intro n (trivial-addition-rearrangement (g i) n 1)


      fact₁ : ∀(i : ℕ) → K(α(g i) ≡ ₁)
      fact₁ 0 = h 0
      fact₁ (succ i) = h(g i + 1)
