Martin Escardo and Paulo Oliva 2011

\begin{code}

{-# OPTIONS --without-K #-}

module InfinitePigeon.J-Shift where

\end{code}

Import Pigeon.one of J-Shift-BBC or J-Shift-Selection.

\begin{code}

open import InfinitePigeon.J-Shift-Selection        -- Choose here...
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.Logic
open import InfinitePigeon.Naturals

\end{code}

Use one of K-∀-shift-bbc or K-∀-shift-mbr or K-∀-shift-selection:

\begin{code}

J-∀-shift : {R : Ω} {A : ℕ → Ω} →
---------

   (∀(n : ℕ) → J(A n)) → J {R} (∀(n : ℕ) → A n)

J-∀-shift = J-∀-shift-selection     -- ... and here accordingly.

\end{code}
