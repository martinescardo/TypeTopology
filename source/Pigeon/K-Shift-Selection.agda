-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K --exact-split #-}

module Pigeon.K-Shift-Selection where

open import Pigeon.J-Shift-Selection
open import Pigeon.JK-Monads
open import Pigeon.Logic
open import Pigeon.Naturals


K-∀-shift-selection : {R : Ω} {A : ℕ → Ω} →
-------------------

            (∀(n : ℕ) → R → A n) →                   -- efqs,
            (∀(n : ℕ) → K(A n)) → K(∀(n : ℕ) → A n)  -- shift.

K-∀-shift-selection efqs φs = J-K(J-∀-shift-selection(λ n → K-J(efqs n) (φs n)))
