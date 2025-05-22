Theo Hepburn, started in February 2025

Defines the two evaluation strategies that we can use: lazy and eager.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TGH.Strategy where

open import MLTT.Spartan

data Strategy : 𝓤₀ ̇ where
 lazy : Strategy
 eager : Strategy
  
\end{code}
