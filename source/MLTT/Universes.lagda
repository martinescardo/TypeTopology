\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Universes where

open import Agda.Primitive public
  using (_⊔_)
  renaming (lzero to 𝓤₀
          ; lsuc to _⁺
          ; Level to Universe
          ; Setω to 𝓤ω
          )

variable
 𝓤 𝓥 𝓦 𝓣 𝓤' 𝓥' 𝓦' 𝓣' : Universe

\end{code}

The following should be the only use of the Agda keyword `Set` in this
development:

\begin{code}

_̇ : (𝓤 : Universe) → Set (𝓤 ⁺)
𝓤 ̇ = Set 𝓤

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺

_⁺⁺ : Universe → Universe
𝓤 ⁺⁺ = 𝓤 ⁺ ⁺

\end{code}

precedences:

\begin{code}

infix  1 _̇

\end{code}
