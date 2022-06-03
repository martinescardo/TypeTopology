Alternative of _+_:

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module AlternativePlus where

open import Universes
open import Two
open import Sigma

_+'_ : 𝓤 ̇ → 𝓤 ̇ → 𝓤 ̇
X₀ +' X₁ = Σ i ꞉ 𝟚 , 𝟚-cases X₀ X₁ i

\end{code}
