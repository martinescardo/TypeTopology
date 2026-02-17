Martin Escardo, Paulo Oliva, originally 2023, with universes
generalized in March 2024.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module MonadOnTypes.K where

open import MonadOnTypes.Definition

𝕂 : 𝓦₀ ̇ → Monad {λ 𝓤 → 𝓦₀ ⊔ 𝓤}
𝕂 {𝓦₀} R = record {
       functor = λ X → (X → R) → R ;
       η       = λ x p → p x ;
       ext     = λ f ϕ p → ϕ (λ x → f x p) ;
       ext-η   = λ x → refl ;
       unit    = λ f x → refl ;
       assoc   = λ g f x → refl
     }

module K-definitions (R : 𝓦₀ ̇ ) where

 K : 𝓤 ̇ → 𝓦₀ ⊔ 𝓤 ̇
 K = functor (𝕂 R)

 _⊗ᴷ_ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
      → K X
      → ((x : X) → K (Y x))
      → K (Σ x ꞉ X , Y x)
 _⊗ᴷ_ = _⊗_ (𝕂 R)

 ⊗ᴷ-direct-definition : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                        (ϕ : K X)
                        (γ : (x : X) → K (Y x))
                      → ϕ ⊗ᴷ γ ∼ (λ q → ϕ (λ x → γ x (curry q x)))
 ⊗ᴷ-direct-definition ϕ γ q = refl

 ηᴷ : {X : 𝓤 ̇ } → X → K X
 ηᴷ = η (𝕂 R)

 extᴷ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → K Y) → K X → K Y
 extᴷ = ext (𝕂 R)

 mapᴷ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → K X → K Y
 mapᴷ = map (𝕂 R)

\end{code}
