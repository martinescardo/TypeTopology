\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Natural-Numbers-Type where

open import MLTT.Universes

data ℕ : 𝓤₀ ̇  where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

\end{code}
