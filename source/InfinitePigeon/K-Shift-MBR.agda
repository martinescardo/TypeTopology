-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K --no-termination-check #-}

-- We use Berger's modified bar recursion functional to realize the
-- K-Shift.

module InfinitePigeon.K-Shift-MBR where

open import InfinitePigeon.Finite
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.Logic
open import InfinitePigeon.LogicalFacts
open import InfinitePigeon.Naturals

K-∀-shift-mbr : {R : Ω} {A : ℕ → Ω} →
-------------
            (∀(n : ℕ) → R → A n) →                   -- efqs,
            (∀(n : ℕ) → K(A n)) → K(∀(n : ℕ) → A n)  -- shift.

K-∀-shift-mbr {R} {A} efqs φs p = mbr {0} (λ ())
  where
   mbr : {m : ℕ} → (∀(i : smaller m) → A(embed i)) → R
   mbr {m} s = p(override s (λ n → efqs n (φs m (λ x → mbr(append {A} s x)))))
