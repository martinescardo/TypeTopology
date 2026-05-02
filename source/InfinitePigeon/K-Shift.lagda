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

\end{code}

Choose a definition here for experimentation:

 0. K-∀-shift-selection
 1. K-∀-shift-mbr
 2. InfinitePigeon.K-Shift-BBC.K-∀-shift-bbc

\begin{code}

choice : ℕ
choice = 0

K-∀-shift : {R : Ω}
            {A : ℕ → Ω}
          → (∀(n : ℕ) → R → A n)                               -- efqs,
          → (∀(n : ℕ) → K {R} (A n)) → K {R} (∀(n : ℕ) → A n)  -- shift.
K-∀-shift = g choice
 where
  g : ℕ → _
  g O               = K-∀-shift-selection
  g 1               = K-∀-shift-mbr
  g (succ (succ _)) = K-∀-shift-bbc

\end{code}
