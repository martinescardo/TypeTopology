-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K #-}

module InfinitePigeon.K-Shift-BBC where

open import InfinitePigeon.J-Shift-BBC
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.Logic
open import InfinitePigeon.Naturals


K-∀-shift-bbc : {R : Ω} {A : ℕ → Ω} →
-------------

            (∀(n : ℕ) → R → A n) →                   -- efqs,
            (∀(n : ℕ) → K(A n)) → K(∀(n : ℕ) → A n)  -- shift.

K-∀-shift-bbc efqs φs = J-K(J-∀-shift-bbc(λ n → K-J(efqs n) (φs n)))
