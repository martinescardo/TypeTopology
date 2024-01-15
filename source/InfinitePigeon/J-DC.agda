-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K #-}

module InfinitePigeon.J-DC where

open import InfinitePigeon.Addition
open import InfinitePigeon.Choice
open import InfinitePigeon.Equality
open import InfinitePigeon.J-Shift
open import InfinitePigeon.JK-LogicalFacts
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.Logic
open import InfinitePigeon.LogicalFacts
open import InfinitePigeon.Naturals

-----------------------------------------------------------
--                                                       --
-- Translation of dependent choice for a particular case --
--                                                       --
-----------------------------------------------------------

J-∀-double-shift : {R : Ω} {P : ℕ → ℕ → ℕ → Ω} →
---------------
     (∀(n : ℕ) → ∀(x : ℕ) → J∃ \(y : ℕ) → P n x y) →
     J(∀(n : ℕ) → ∀(x : ℕ) → ∃ \(y : ℕ) → P n x y)

J-∀-double-shift {R} f = J-∀-shift {R} (λ n → J-∀-shift (f n))


J-DC-ℕ : {R : Ω} {P : ℕ → ℕ → ℕ → Ω} →
-------
      ∀(x₀ : ℕ) →
     (∀(n : ℕ) → ∀(x : ℕ) → J∃ \(y : ℕ) → P n x y) →
     J∃ \(α : ℕ → ℕ) → α O ≡ x₀ ∧ (∀(n : ℕ) → P n (α n) (α(n + 1)))

J-DC-ℕ {R} x₀ f = (J-functor {R} (DC x₀)) (J-∀-double-shift f)
