-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K --exact-split #-}

module Pigeon.K-DC where

open import Pigeon.Addition
open import Pigeon.Choice
open import Pigeon.Equality
open import Pigeon.JK-LogicalFacts
open import Pigeon.JK-Monads
open import Pigeon.K-Shift
open import Pigeon.Logic
open import Pigeon.Naturals

-------------------------------------------------------------
--                                                         --
-- The K-translation of dependent choice of ground type.   --
--                                                         --
-------------------------------------------------------------

K-∀-double-shift : {R : Ω} {P : ℕ → ℕ → ℕ → Ω} →
---------------
     (∀(n : ℕ) → ∀(x : ℕ) → R → ∃ \(y : ℕ) → P n x y) →  -- efqs
     (∀(n : ℕ) → ∀(x : ℕ) → K∃ \(y : ℕ) → P n x y) →     -- premise
     K(∀(n : ℕ) → ∀(x : ℕ) → ∃ \(y : ℕ) → P n x y)       -- conclusion

K-∀-double-shift {R} {P} efqs f
  = K-∀-shift {R} efqs' (λ n → K-∀-shift (efqs n) (f n))
 where
  efqs' : (∀(n : ℕ) → R → ∀(x : ℕ) → ∃ \(y : ℕ) → P n x y)
  efqs' n r x = efqs n x r


K-DC-ℕ : {R : Ω} {P : ℕ → ℕ → ℕ → Ω} →
-------
    (∀(n : ℕ) → ∀(x : ℕ) → R → ∃ \(y : ℕ) → P n x y)
 →  ∀(x₀ : ℕ)
 → (∀(n : ℕ) → ∀(x : ℕ) → K∃ \(y : ℕ) → P n x y)
 → K∃ \(α : ℕ → ℕ) → α O ≡ x₀ ∧ (∀(n : ℕ) → P n (α n) (α(n + 1)))

K-DC-ℕ efqs x₀ f = (K-functor (DC x₀)) (K-∀-double-shift efqs f)
