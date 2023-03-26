Martin Escardo

Brouwer ordinal codes.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module Ordinals.Brouwer where

open import MLTT.Spartan

data B : 𝓤₀ ̇ where
 Z : B
 S : B → B
 L : (ℕ → B) → B

\end{code}
