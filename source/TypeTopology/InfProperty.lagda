Martin Escardo 20-21 December 2012

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import MLTT.Two-Properties
open import TypeTopology.CompactTypes

module TypeTopology.InfProperty {𝓤 𝓥} {X : 𝓤 ̇ } (_≤_ : X → X → 𝓥 ̇ ) where

conditional-root : (X → 𝟚) → X → 𝓤 ̇
conditional-root p x₀ = (Σ x ꞉ X , p x ＝ ₀) → p x₀ ＝ ₀

root-lower-bound : (X → 𝟚) → X → 𝓤 ⊔ 𝓥 ̇
root-lower-bound p l = (x : X) → p x ＝ ₀ → l ≤ x

upper-bound-of-root-lower-bounds : (X → 𝟚) → X → 𝓤 ⊔ 𝓥 ̇
upper-bound-of-root-lower-bounds p u = (l : X) → root-lower-bound p l → l ≤ u

roots-infimum : (X → 𝟚) → X → 𝓤 ⊔ 𝓥 ̇
roots-infimum p x = root-lower-bound p x × upper-bound-of-root-lower-bounds p x

has-inf : 𝓤 ⊔ 𝓥 ̇
has-inf = (p : X → 𝟚) → Σ x ꞉ X , conditional-root p x × roots-infimum p x

has-inf-gives-compact∙ : has-inf → is-compact∙ X
has-inf-gives-compact∙ h p = f (h p)
 where
  f : (Σ x₀ ꞉ X , conditional-root p x₀ × roots-infimum p x₀)
    → (Σ x₀ ꞉ X , (p x₀ ＝ ₁ → (x : X) → p x ＝ ₁))
  f (x₀ , g , _) = (x₀ , k)
   where
    g' : p x₀ ≠ ₀ → ¬ (Σ x ꞉ X , p x ＝ ₀)
    g' = contrapositive g

    u : ¬ (Σ x ꞉ X , p x ＝ ₀) → (x : X) → p x ＝ ₁
    u ν x = different-from-₀-equal-₁ (λ (e : p x ＝ ₀) → ν (x , e))

    k : p x₀ ＝ ₁ → (x : X) → p x ＝ ₁
    k e = u (g' (equal-₁-different-from-₀ e))

has-inf-gives-compact : has-inf → is-compact X
has-inf-gives-compact = compact∙-types-are-compact ∘ has-inf-gives-compact∙

has-inf-gives-Compact : {𝓦 : Universe} → has-inf → is-Compact X {𝓦}
has-inf-gives-Compact = compact-types-are-Compact ∘ has-inf-gives-compact

\end{code}
