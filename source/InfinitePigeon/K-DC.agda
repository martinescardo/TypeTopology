-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K #-}

module InfinitePigeon.K-DC where

open import InfinitePigeon.Addition
open import InfinitePigeon.Choice
open import InfinitePigeon.Equality
open import InfinitePigeon.JK-LogicalFacts
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.K-Shift
open import InfinitePigeon.Logic
open import InfinitePigeon.Naturals

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
