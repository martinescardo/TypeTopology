Martin Escardo

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Two-Prop-Density where

open import SpartanMLTT
open import Negation
open import Two-Properties
open import UF-Base
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-Embeddings
open import UF-PropTrunc
open import UF-ExcludedMiddle

⊥-⊤-density : funext 𝓤 𝓤 → propext 𝓤 → (f : Ω 𝓤 → 𝟚)
            → f ⊥ ≡ ₁ → f ⊤ ≡ ₁ → (p : Ω 𝓤) → f p ≡ ₁
⊥-⊤-density fe pe f r s p = Lemma[b≢₀→b≡₁] a
 where
    a : f p ≢ ₀
    a t = 𝟘-elim(no-truth-values-other-than-⊥-or-⊤ fe pe (p , (b , c)))
      where
        b : p ≢ ⊥
        b u = zero-is-not-one (t ⁻¹ ∙ ap f u ∙ r)
        c : p ≢ ⊤
        c u = zero-is-not-one (t ⁻¹ ∙ ap f u ∙ s)

𝟚inΩ : 𝟚 → Ω 𝓤
𝟚inΩ ₀ = ⊥
𝟚inΩ ₁ = ⊤

𝟚inΩ-embedding : funext 𝓤 𝓤 → propext 𝓤 → is-embedding (𝟚inΩ {𝓤})
𝟚inΩ-embedding fe pe (P , isp) (₀ , p) (₀ , q) = to-Σ-≡ (refl , Ω-is-a-set fe pe p q)
𝟚inΩ-embedding fe pe (P , isp) (₀ , p) (₁ , q) = 𝟘-elim (⊥-is-not-⊤ (p ∙ q ⁻¹))
𝟚inΩ-embedding fe pe (P , isp) (₁ , p) (₀ , q) = 𝟘-elim (⊥-is-not-⊤ (q ∙ p ⁻¹))
𝟚inΩ-embedding fe pe (P , isp) (₁ , p) (₁ , q) = to-Σ-≡ (refl , Ω-is-a-set fe pe p q)

\end{code}
