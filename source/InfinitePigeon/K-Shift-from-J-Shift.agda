-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K #-}

module InfinitePigeon.K-Shift-from-J-Shift where

open import InfinitePigeon.J-Shift
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.Logic
open import InfinitePigeon.LogicalFacts
open import InfinitePigeon.Naturals

K-∀-shift : {R : Ω} {A : ℕ → Ω} →
---------
            (∀(n : ℕ) → R → A n) →                   -- efqs,
            (∀(n : ℕ) → K(A n)) → K(∀(n : ℕ) → A n)  -- shift.

K-∀-shift efqs φs = J-K(J-∀-shift(λ n → K-J(efqs n) (φs n)))
