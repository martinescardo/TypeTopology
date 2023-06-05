-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K --no-termination-check --exact-split --no-sized-types --no-guardedness --auto-inline #-}

-- We use Berger's modified bar recursion functional to realize the
-- K-Shift.

module Pigeon.K-Shift-MBR where

open import Pigeon.Finite
open import Pigeon.JK-Monads
open import Pigeon.Logic
open import Pigeon.LogicalFacts
open import Pigeon.Naturals

K-∀-shift-mbr : {R : Ω} {A : ℕ → Ω} →
-------------
            (∀(n : ℕ) → R → A n) →                   -- efqs,
            (∀(n : ℕ) → K(A n)) → K(∀(n : ℕ) → A n)  -- shift.

K-∀-shift-mbr {R} {A} efqs φs p = mbr {0} (λ ())
  where
   mbr : {m : ℕ} → (∀(i : smaller m) → A(embed i)) → R
   mbr {m} s = p(override s (λ n → efqs n (φs m (λ x → mbr(append {A} s x)))))
