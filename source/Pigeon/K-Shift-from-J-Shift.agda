-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K --exact-split #-}

module Pigeon.K-Shift-from-J-Shift where

open import Pigeon.J-Shift
open import Pigeon.JK-Monads
open import Pigeon.Logic
open import Pigeon.LogicalFacts
open import Pigeon.Naturals

K-∀-shift : {R : Ω} {A : ℕ → Ω} →
---------
            (∀(n : ℕ) → R → A n) →                   -- efqs,
            (∀(n : ℕ) → K(A n)) → K(∀(n : ℕ) → A n)  -- shift.

K-∀-shift efqs φs = J-K(J-∀-shift(λ n → K-J(efqs n) (φs n)))
