Alternative of _+_:

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module MLTT.AlternativePlus where

open import MLTT.Universes
open import MLTT.Two
open import MLTT.Sigma

_+'_ : 𝓤 ̇ → 𝓤 ̇ → 𝓤 ̇
X₀ +' X₁ = Σ i ꞉ 𝟚 , 𝟚-cases X₀ X₁ i

\end{code}
