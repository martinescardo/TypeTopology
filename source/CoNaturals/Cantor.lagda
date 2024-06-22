Martin Escardo.

This short module is to avoid a chain of imports.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module CoNaturals.Cantor where

open import MLTT.Spartan

cons : 𝟚 → (ℕ → 𝟚) → (ℕ → 𝟚)
cons b α 0        = b
cons b α (succ n) = α n

\end{code}
