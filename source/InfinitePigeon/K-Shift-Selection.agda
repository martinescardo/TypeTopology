-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K #-}

module InfinitePigeon.K-Shift-Selection where

open import InfinitePigeon.J-Shift-Selection
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.Logic
open import InfinitePigeon.Naturals


K-∀-shift-selection : {R : Ω} {A : ℕ → Ω} →
-------------------

            (∀(n : ℕ) → R → A n) →                   -- efqs,
            (∀(n : ℕ) → K(A n)) → K(∀(n : ℕ) → A n)  -- shift.

K-∀-shift-selection efqs φs = J-K(J-∀-shift-selection(λ n → K-J(efqs n) (φs n)))
