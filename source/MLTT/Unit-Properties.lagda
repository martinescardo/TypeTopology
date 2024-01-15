One-element type properties.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Unit-Properties where

open import MLTT.Universes
open import MLTT.Unit
open import MLTT.Empty
open import MLTT.Id
open import MLTT.Negation

𝟙-all-⋆ : (x : 𝟙 {𝓤}) → x ＝ ⋆
𝟙-all-⋆ {𝓤} ⋆ = refl {𝓤}
𝟙-is-not-𝟘 : 𝟙 ≠ 𝟘
𝟙-is-not-𝟘 p = transport (λ X → X) p ⋆

\end{code}
