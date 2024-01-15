-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K #-}

module InfinitePigeon.J-Shift where

-- Import Pigeon.one of J-Shift-BBC or J-Shift-Selection.

open import InfinitePigeon.J-Shift-Selection        -- Choose here...
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.Logic
open import InfinitePigeon.Naturals

-- Use one of K-∀-shift-bbc or K-∀-shift-mbr or K-∀-shift-selection:

J-∀-shift : {R : Ω} {A : ℕ → Ω} →
---------

   (∀(n : ℕ) → J(A n)) → J {R} (∀(n : ℕ) → A n)

J-∀-shift = J-∀-shift-selection     -- ... and here accordingly.
