Martin Escardo, original date unknown.

Alternative of _+_:

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.AlternativePlus where

open import MLTT.Universes
open import MLTT.Two
open import MLTT.Sigma

_+'_ : 𝓤 ̇ → 𝓤 ̇ → 𝓤 ̇
X₀ +' X₁ = Σ i ꞉ 𝟚 , 𝟚-cases X₀ X₁ i

\end{code}
