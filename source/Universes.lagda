\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Universes where

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

The following should be the only use of the Agda keyword 'Set' in this
development:

\begin{code}

_̇ : (𝓤 : Universe) → _
𝓤 ̇ = Set 𝓤

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺

\end{code}

Lift a type X in the universe U to a type X ↑ in the universe 𝓤 ⊔ 𝓥.
An element of X is of the form x ↥ for x an element of X.

\begin{code}

record _↑ {𝓤 𝓥} (X : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ̇ where
 constructor _↥
 field _↧ : X
 infix 0 _↧

open _↑ public

infix 0 _↑
infix 0 _↥

\end{code}

precedences:

\begin{code}

infix  1 _̇

\end{code}
