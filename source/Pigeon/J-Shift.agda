-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K --exact-split --no-sized-types --no-guardedness --auto-inline #-}

module Pigeon.J-Shift where

-- Import Pigeon.one of J-Shift-BBC or J-Shift-Selection.

open import Pigeon.J-Shift-Selection        -- Choose here...
open import Pigeon.JK-Monads
open import Pigeon.Logic
open import Pigeon.Naturals

-- Use one of K-∀-shift-bbc or K-∀-shift-mbr or K-∀-shift-selection:

J-∀-shift : {R : Ω} {A : ℕ → Ω} →
---------

   (∀(n : ℕ) → J(A n)) → J {R} (∀(n : ℕ) → A n)

J-∀-shift = J-∀-shift-selection     -- ... and here accordingly.
