-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K --exact-split #-}

module Pigeon.J-DC where

open import Pigeon.Addition
open import Pigeon.Choice
open import Pigeon.Equality
open import Pigeon.J-Shift
open import Pigeon.JK-LogicalFacts
open import Pigeon.JK-Monads
open import Pigeon.Logic
open import Pigeon.LogicalFacts
open import Pigeon.Naturals

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
