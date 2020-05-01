\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

module MGS-Universes where

open import Agda.Primitive public
 renaming (
            Level to Universe -- We speak of universes rather than of levels.
          ; lzero to 𝓤₀       -- Our first universe is called 𝓤₀
          ; lsuc to _⁺        -- The universe after 𝓤 is 𝓤 ⁺
          ; Setω to 𝓤ω        -- There is a universe 𝓤ω strictly above 𝓤₀, 𝓤₁, ⋯ , 𝓤ₙ, ⋯
          )
 using    (_⊔_)               -- Least upper bound of two universes, e.g. 𝓤₀ ⊔ 𝓤₁ is 𝓤₁

Type = λ ℓ → Set ℓ

_̇   : (𝓤 : Universe) → Type (𝓤 ⁺)

𝓤 ̇  = Type 𝓤

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺
𝓤₃ = 𝓤₂ ⁺

_⁺⁺ : Universe → Universe
𝓤 ⁺⁺ = 𝓤 ⁺ ⁺
universe-of : {𝓤 : Universe} (X : 𝓤 ̇ ) → Universe
universe-of {𝓤} X = 𝓤

infix  1 _̇
\end{code}
