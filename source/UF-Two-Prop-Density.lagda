Excluded middle related things.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Two-Prop-Density where

open import SpartanMLTT
open import Two
open import UF-Base
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-Embedding
open import UF-PropTrunc
open import UF-ExcludedMiddle

⊥-⊤-density : ∀ {U} → funext U U → propext U → (f : Ω U → 𝟚)
            → f ⊥ ≡ ₁ → f ⊤ ≡ ₁ → (p : Ω U) → f p ≡ ₁
⊥-⊤-density fe pe f r s p = Lemma[b≢₀→b≡₁] a
 where
    a : f p ≢ ₀
    a t = 𝟘-elim(no-truth-values-other-than-⊥-or-⊤ fe pe (p , (b , c)))
      where
        b : p ≢ ⊥
        b u = zero-is-not-one (t ⁻¹ ∙ ap f u ∙ r)
        c : p ≢ ⊤
        c u = zero-is-not-one (t ⁻¹ ∙ ap f u ∙ s)

𝟚inΩ : ∀ {U} → 𝟚 → Ω U
𝟚inΩ ₀ = ⊥
𝟚inΩ ₁ = ⊤

𝟚inΩ-embedding : ∀ {U} → funext U U → propext U → is-embedding (𝟚inΩ {U})
𝟚inΩ-embedding fe pe (P , isp) (₀ , p) (₀ , q) = to-Σ-≡ (refl , Ω-is-set fe pe p q)
𝟚inΩ-embedding fe pe (P , isp) (₀ , p) (₁ , q) = 𝟘-elim (⊥-is-not-⊤ (p ∙ q ⁻¹))
𝟚inΩ-embedding fe pe (P , isp) (₁ , p) (₀ , q) = 𝟘-elim (⊥-is-not-⊤ (q ∙ p ⁻¹))
𝟚inΩ-embedding fe pe (P , isp) (₁ , p) (₁ , q) = to-Σ-≡ (refl , Ω-is-set fe pe p q)

\end{code}
