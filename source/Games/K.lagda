Martin Escardo, Paulo Oliva, 2023

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module Games.K where

open import Games.Monad

𝕂 : Type → Monad
𝕂 R = record {
       functor = λ X → (X → R) → R ;
       η       = λ x p → p x ;
       ext     = λ f ϕ p → ϕ (λ x → f x p) ;
       ext-η   = λ x → refl ;
       unit    = λ f x → refl ;
       assoc   = λ g f x → refl
      }

module K-definitions (R : Type) where

 K : Type → Type
 K = functor (𝕂 R)

 _⊗ᴷ_ : {X : Type} {Y : X → Type}
      → K X
      → ((x : X) → K (Y x))
      → K (Σ x ꞉ X , Y x)
 _⊗ᴷ_ = _⊗_ (𝕂 R)

 ⊗ᴷ-direct-definition : {X : Type} {Y : X → Type}
                        (ϕ : K X)
                        (γ : (x : X) → K (Y x))
                      → ϕ ⊗ᴷ γ ∼ (λ q → ϕ (λ x → γ x (curry q x)))
 ⊗ᴷ-direct-definition ϕ γ q = refl

 ηᴷ : {X : Type} → X → K X
 ηᴷ = η (𝕂 R)

 extᴷ : {X Y : Type} → (X → K Y) → K X → K Y
 extᴷ = ext (𝕂 R)

 mapᴷ : {X Y : Type} → (X → Y) → K X → K Y
 mapᴷ = map (𝕂 R)

\end{code}
