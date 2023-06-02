-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K --exact-split --no-sized-types --no-guardedness --auto-inline #-}

module Pigeon.K-AC-N where

open import Pigeon.Choice
open import Pigeon.JK-LogicalFacts
open import Pigeon.JK-Monads
open import Pigeon.K-Shift
open import Pigeon.Logic
open import Pigeon.LogicalFacts
open import Pigeon.Naturals

-----------------------------------------------------------------------
-- The K-translation of countable choice AC-N can be proved only for --
-- certain formulas, including those that are in the image of the    --
-- K-translation.                                                    --
--                                                                   --
-- Hence we have a restriction efq (ex falso quadlibet).             --
--                                                                   --
-- This is because there is no general K-∀-shift.                    --
-----------------------------------------------------------------------


K-AC-ℕ : {R : Ω} {X : ℕ → Set} {P : (n : ℕ) → X n → Ω} →
-------
        (∀(n : ℕ) → R → ∃ \(m : X n) → P n m)               -- efqs,
      → (∀(n : ℕ) → K∃ \(m : X n) → P n m)                  -- premise,
      → K∃ \(f : ((n : ℕ) → X n)) → ∀(n : ℕ) → P n (f n)    -- conclusion.

K-AC-ℕ efqs = (K-functor AC) ∘ (K-∀-shift efqs)
