{-# OPTIONS --without-K --exact-split --safe #-}

module Universes where

open import Agda.Primitive public
  using (_⊔_)
  renaming (lzero to 𝓤₀             -- Our first universe is called 𝓤₀
          ; lsuc to _⁺              -- The universe after 𝓤 is 𝓤 ⁺
          ; Level to Universe       -- We speak of universes rather than of levels.
          ; Setω to 𝓤ω
          )

Type = λ ℓ → Set ℓ

_̇ : (𝓤 : Universe) → Type (𝓤 ⁺)
𝓤 ̇ = Type 𝓤

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺

universe-of : {𝓤 : Universe} (X : 𝓤 ̇) → Universe
universe-of {𝓤} X = 𝓤

infix  1 _̇

