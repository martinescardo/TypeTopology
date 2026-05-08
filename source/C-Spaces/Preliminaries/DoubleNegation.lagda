Chuangjie Xu 2013 (ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module C-Spaces.Preliminaries.DoubleNegation where

open import MLTT.Spartan
open import UF.Base

\end{code}

Some properties of the double negation monad

\begin{code}

¬¬𝟘-elim : {X : Set} → ¬¬ (𝟘 {𝓤₀}) → X
¬¬𝟘-elim f = 𝟘-elim (f λ ())

¬¬-functor₂ : {X Y Z : Set} → (X → Y → Z) → ¬¬ X → ¬¬ Y → ¬¬ Z
¬¬-functor₂ f xh yh = ¬¬-kleisli (λ x → ¬¬-functor (f x) yh) xh

\end{code}

The double negations of identity type and related properties:

\begin{code}

¬¬refl : {X : Set} {x : X}
       → ¬¬ (x ＝ x)
¬¬refl = ¬¬-intro refl

¬¬sym : {X : Set} {x₀ x₁ : X}
      → ¬¬ (x₀ ＝ x₁) → ¬¬ (x₁ ＝ x₀)
¬¬sym = ¬¬-functor _⁻¹

¬¬trans : {X : Set} {x₀ x₁ x₂ : X}
        → ¬¬ (x₀ ＝ x₁) → ¬¬ (x₁ ＝ x₂) → ¬¬ (x₀ ＝ x₂)
¬¬trans = ¬¬-functor₂ _∙_

¬¬transport : {X : Set} {x x' : X} (Y : X → Set)
            → ¬¬ (x ＝ x') → ¬¬ Y x → ¬¬ Y x'
¬¬transport Y = ¬¬-functor₂ (transport Y)

¬¬ap : {X Y : Set} (f : X → Y) {x₀ x₁ : X}
     → ¬¬ (x₀ ＝ x₁) → ¬¬ (f x₀ ＝ f x₁)
¬¬ap f = ¬¬-functor (ap f)

¬¬happly : {X Y : Set} {f g : X → Y}
         → ¬¬ (f ＝ g) → ∀ x → ¬¬ (f x ＝ g x)
¬¬happly eh x = ¬¬-functor (λ e → happly e x) eh

¬¬to-Σ-＝ : {X : Set} {A : X → Set} {σ τ : Σ A}
        → (Σ p ꞉ pr₁ σ ＝ pr₁ τ , ¬¬ (transport A p (pr₂ σ) ＝ pr₂ τ))
        → ¬¬ (σ ＝ τ)
¬¬to-Σ-＝ (p , f) = ¬¬-functor (λ g → to-Σ-＝ (p , g)) f

¬¬to-×-＝ : {X Y : Set} {x x' : X} {y y' : Y}
         → ¬¬ (x ＝ x') → ¬¬ (y ＝ y')
         → ¬¬ ((x , y) ＝ (x' , y'))
¬¬to-×-＝ = ¬¬-functor₂ to-×-＝

\end{code}
