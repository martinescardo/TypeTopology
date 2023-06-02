-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K --exact-split --no-sized-types --no-guardedness --auto-inline #-}

module Pigeon.K-Shift-BBC where

open import Pigeon.J-Shift-BBC
open import Pigeon.JK-Monads
open import Pigeon.Logic
open import Pigeon.Naturals


K-∀-shift-bbc : {R : Ω} {A : ℕ → Ω} →
-------------

            (∀(n : ℕ) → R → A n) →                   -- efqs,
            (∀(n : ℕ) → K(A n)) → K(∀(n : ℕ) → A n)  -- shift.

K-∀-shift-bbc efqs φs = J-K(J-∀-shift-bbc(λ n → K-J(efqs n) (φs n)))
