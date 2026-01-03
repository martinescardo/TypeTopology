Martin Escardo and Paulo Oliva 2011

\begin{code}

{-# OPTIONS --without-K #-}

module InfinitePigeon.K-Shift where

\end{code}

This is a wrapper module. Perform a choice below.

\begin{code}

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

\end{code}

Choose here:

\begin{code}

K-∀-shift = K-∀-shift-selection
-- K-∀-shift = K-∀-shift-mbr
-- K-∀-shift = K-∀-shift-bbc

\end{code}
