Chuangjie Xu 2013 (ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module C-Spaces.Preliminaries.DoubleNegation where

open import MLTT.Spartan
open import UF.Base

\end{code}

Some properties of the double negation monad

\begin{code}

¬¬𝟘-elim : {X : 𝓤₀ ̇ } → ¬¬ (𝟘 {𝓤₀}) → X
¬¬𝟘-elim f = 𝟘-elim (f id)

¬¬-functor₂ : {X Y Z : 𝓤₀ ̇ } → (X → Y → Z) → ¬¬ X → ¬¬ Y → ¬¬ Z
¬¬-functor₂ f xh yh = ¬¬-kleisli (λ x → ¬¬-functor (f x) yh) xh

\end{code}

The double negations of identity type and related properties:

\begin{code}

¬¬refl : {X : 𝓤₀ ̇ } {x : X}
       → ¬¬ (x ＝ x)
¬¬refl = ¬¬-intro refl

¬¬sym : {X : 𝓤₀ ̇ } {x₀ x₁ : X}
      → ¬¬ (x₀ ＝ x₁) → ¬¬ (x₁ ＝ x₀)
¬¬sym = ¬¬-functor _⁻¹

¬¬trans : {X : 𝓤₀ ̇ } {x₀ x₁ x₂ : X}
        → ¬¬ (x₀ ＝ x₁) → ¬¬ (x₁ ＝ x₂) → ¬¬ (x₀ ＝ x₂)
¬¬trans = ¬¬-functor₂ _∙_

¬¬transport : {X : 𝓤₀ ̇ } {x x' : X} (Y : X → 𝓤₀ ̇ )
            → ¬¬ (x ＝ x') → ¬¬ Y x → ¬¬ Y x'
¬¬transport Y = ¬¬-functor₂ (transport Y)

¬¬ap : {X Y : 𝓤₀ ̇ } (f : X → Y) {x₀ x₁ : X}
     → ¬¬ (x₀ ＝ x₁) → ¬¬ (f x₀ ＝ f x₁)
¬¬ap f = ¬¬-functor (ap f)

¬¬happly : {X Y : 𝓤₀ ̇ } {f g : X → Y}
         → ¬¬ (f ＝ g) → ∀ x → ¬¬ (f x ＝ g x)
¬¬happly eh x = ¬¬-functor (λ e → happly e x) eh

¬¬to-Σ-＝ : {X : 𝓤₀ ̇ } {A : X → 𝓤₀ ̇ } {σ τ : Σ A}
        → (Σ p ꞉ pr₁ σ ＝ pr₁ τ , ¬¬ (transport A p (pr₂ σ) ＝ pr₂ τ))
        → ¬¬ (σ ＝ τ)
¬¬to-Σ-＝ (p , f) = ¬¬-functor (λ g → to-Σ-＝ (p , g)) f

¬¬to-×-＝ : {X Y : 𝓤₀ ̇ } {x x' : X} {y y' : Y}
         → ¬¬ (x ＝ x') → ¬¬ (y ＝ y')
         → ¬¬ ((x , y) ＝ (x' , y'))
¬¬to-×-＝ = ¬¬-functor₂ to-×-＝

\end{code}
