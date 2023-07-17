-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K --exact-split #-}

module Pigeon.K-Shift where

-- This is a wrapper module. Perform a choice below.

open import Pigeon.JK-Monads
open import Pigeon.K-Shift-BBC
open import Pigeon.K-Shift-MBR
open import Pigeon.K-Shift-Selection
open import Pigeon.Logic
open import Pigeon.Naturals


K-∀-shift : {R : Ω} {A : ℕ → Ω} →
---------

   (∀(n : ℕ) → R → A n) →                             -- efqs,
   (∀(n : ℕ) → K {R} (A n)) → K {R} (∀(n : ℕ) → A n)  -- shift.


-- Choose here:

K-∀-shift = K-∀-shift-selection
-- K-∀-shift = K-∀-shift-mbr
-- K-∀-shift = K-∀-shift-bbc
