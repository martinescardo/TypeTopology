Theo Hepburn, started October 2024.

Contains an Agda formalisation of the definition of Big O.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TGH.BigO where

open import MLTT.Spartan
open import Naturals.Multiplication
open import Naturals.Order renaming (_≤ℕ_ to _≤_)

data _∈O[_] (f : ℕ → ℕ) (g : ℕ → ℕ) : 𝓤₀  ̇ where
 big-o : Σ c ꞉ ℕ , Σ N₀ ꞉ ℕ , Π N ꞉ ℕ , (N₀ ≤ N → f N ≤ c * (g N))
      → f ∈O[ g ]
      
\end{code}
