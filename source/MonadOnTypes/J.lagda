Martin Escardo, Paulo Oliva, 2023

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module MonadOnTypes.J where

open import UF.FunExt
open import MonadOnTypes.Construction

𝕁 : Type → Monad
𝕁 R = record {
 functor = λ X → (X → R) → X ;
 η       = λ x p → x ;
 ext     = λ f ε p → f (ε (λ x → p (f x p))) p ;
 ext-η   = λ ε → refl ;
 unit    = λ f x → refl ;
 assoc   = λ g f x → refl
 }

module J-definitions (R : Type) where

 J : Type → Type
 J = functor (𝕁 R)

 _⊗ᴶ_ : {X : Type} {Y : X → Type}
      → J X
      → ((x : X) → J (Y x))
      → J (Σ x ꞉ X , Y x)
 _⊗ᴶ_ = _⊗_ (𝕁 R)

 ⊗ᴶ-direct-definition : {X : Type} {Y : X → Type}
                        (ε : J X)
                        (δ : (x : X) → J (Y x))
                      → ε ⊗ᴶ δ ∼ (λ q → let
                                         ν  = λ x → δ x (curry q x)
                                         x₀ = ε (λ x → curry q x (ν x))
                                        in (x₀ , ν x₀))
 ⊗ᴶ-direct-definition ε δ q = refl

 ηᴶ : {X : Type} → X → J X
 ηᴶ = η (𝕁 R)

 extᴶ : {X Y : Type} → (X → J Y) → J X → J Y
 extᴶ = ext (𝕁 R)

 mapᴶ : {X Y : Type} → (X → Y) → J X → J Y
 mapᴶ = map (𝕁 R)

\end{code}
