Martin Escardo 20-21 December 2012

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import MLTT.Two-Properties
open import TypeTopology.CompactTypes

module Ordinals.InfProperty {𝓤 𝓥} {X : 𝓤 ̇ } (_≤_ : X → X → 𝓥 ̇ ) where

is-conditional-root : (X → 𝟚) → X → 𝓤 ̇
is-conditional-root p x₀ = (Σ x ꞉ X , p x ＝ ₀) → p x₀ ＝ ₀

is-roots-lower-bound : (X → 𝟚) → X → 𝓤 ⊔ 𝓥 ̇
is-roots-lower-bound p l = (x : X) → p x ＝ ₀ → l ≤ x

is-upper-bound-of-lower-bounds : (X → 𝟚) → X → 𝓤 ⊔ 𝓥 ̇
is-upper-bound-of-lower-bounds p u = (l : X) → is-roots-lower-bound p l → l ≤ u

is-roots-infimum : (X → 𝟚) → X → 𝓤 ⊔ 𝓥 ̇
is-roots-infimum p x = is-roots-lower-bound p x
                     × is-upper-bound-of-lower-bounds p x

has-inf : 𝓤 ⊔ 𝓥 ̇
has-inf = (p : X → 𝟚) → Σ x ꞉ X , is-conditional-root p x × is-roots-infimum p x

has-inf-gives-compact∙ : has-inf → is-compact∙ X
has-inf-gives-compact∙ h p = f (h p)
 where
  f : (Σ x₀ ꞉ X , is-conditional-root p x₀ × is-roots-infimum p x₀)
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

Added 28th August 2026. The infimum of a non-empty complemented subset
is a least element.

\begin{code}

is-least-root : (X → 𝟚) → X → 𝓤 ⊔ 𝓥 ̇
is-least-root p x₀ = (p x₀ ＝ ₀) × is-roots-lower-bound p x₀

has-inf-gives-least-root : has-inf
                         → (p : X → 𝟚)
                         → ¬¬ (Σ x ꞉ X , p x ＝ ₀)
                         → Σ x₀ ꞉ X , is-least-root p x₀
has-inf-gives-least-root h p ν = f (h p)
 where
  f : (Σ x₀ ꞉ X , is-conditional-root p x₀ × is-roots-infimum p x₀)
    → Σ x₀ ꞉ X , is-least-root p x₀
  f (x₀ , cr , (lb , _)) = γ (has-inf-gives-compact h p)
   where
    γ : (Σ x ꞉ X , p x ＝ ₀) + (Π x ꞉ X , p x ＝ ₁)
      → Σ x₀ ꞉ X , is-least-root p x₀
    γ (inl σ) = x₀ , cr σ , lb
    γ (inr u) = 𝟘-elim (ν (λ (x , e) → zero-is-not-one (e ⁻¹ ∙ u x)))

\end{code}

Added 2nd September 2026. The least element property for complemented
subsets.

\begin{code}

has-least-roots : 𝓤 ⊔ 𝓥 ̇
has-least-roots = (p : X → 𝟚)
                → ¬¬ (Σ x ꞉ X , p x ＝ ₀)
                → Σ x₀ ꞉ X , is-least-root p x₀

has-inf-gives-least-roots : has-inf → has-least-roots
has-inf-gives-least-roots = has-inf-gives-least-root

\end{code}
