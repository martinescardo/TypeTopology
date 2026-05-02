Martin Escardo and Paulo Oliva 2011

\begin{code}

{-# OPTIONS --without-K #-}

module InfinitePigeon.K-Shift where

\end{code}

This is a wrapper module. Perform a choice below.

\begin{code}

open import InfinitePigeon.JK-Monads
import InfinitePigeon.K-Shift-BBC
import InfinitePigeon.K-Shift-MBR
import InfinitePigeon.K-Shift-Selection
open import InfinitePigeon.Logic
open import InfinitePigeon.Naturals


K-∀-shift : {R : Ω}
            {A : ℕ → Ω}
          → (∀(n : ℕ) → R → A n)                               -- efqs,
          → (∀(n : ℕ) → K {R} (A n)) → K {R} (∀(n : ℕ) → A n)  -- shift.

\end{code}

Choose a definition here for experimentation:

\begin{code}

K-∀-shift =
 InfinitePigeon.K-Shift-Selection.K-∀-shift-selection
-- InfinitePigeon.K-Shift-MBR.K-∀-shift-mbr
-- InfinitePigeon.K-Shift-BBC.K-∀-shift-bbc

\end{code}
