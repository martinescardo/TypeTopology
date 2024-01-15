-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K #-}

module InfinitePigeon.K-Shift where

-- This is a wrapper module. Perform a choice below.

open import InfinitePigeon.JK-Monads
open import InfinitePigeon.K-Shift-BBC
open import InfinitePigeon.K-Shift-MBR
open import InfinitePigeon.K-Shift-Selection
open import InfinitePigeon.Logic
open import InfinitePigeon.Naturals


K-∀-shift : {R : Ω} {A : ℕ → Ω} →
---------

   (∀(n : ℕ) → R → A n) →                             -- efqs,
   (∀(n : ℕ) → K {R} (A n)) → K {R} (∀(n : ℕ) → A n)  -- shift.


-- Choose here:

K-∀-shift = K-∀-shift-selection
-- K-∀-shift = K-∀-shift-mbr
-- K-∀-shift = K-∀-shift-bbc
