Martin Escardo, Paulo Oliva, originally 2023, with universes
generalized in March 2024.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module MonadOnTypes.J where

open import MonadOnTypes.Definition

𝕁 : 𝓦₀ ̇ → Monad {λ 𝓤 → 𝓦₀ ⊔ 𝓤}
𝕁 {𝓦₀} R = record {
 functor = λ X → (X → R) → X ;
 η       = λ x p → x ;
 ext     = λ f ε p → f (ε (λ x → p (f x p))) p ;
 ext-η   = λ ε → refl ;
 unit    = λ f x → refl ;
 assoc   = λ g f x → refl
 }

module J-definitions {R : 𝓦₀ ̇ } where

 J : 𝓤 ̇ → 𝓦₀ ⊔ 𝓤 ̇
 J = functor (𝕁 R)

 _⊗ᴶ_ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
      → J X
      → ((x : X) → J (Y x))
      → J (Σ x ꞉ X , Y x)
 _⊗ᴶ_ = _⊗_ (𝕁 R)

 ⊗ᴶ-direct-definition : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                        (ε : J X)
                        (δ : (x : X) → J (Y x))
                      → ε ⊗ᴶ δ ∼ (λ q → let
                                         ν  = λ x → δ x (curry q x)
                                         x₀ = ε (λ x → curry q x (ν x))
                                        in (x₀ , ν x₀))
 ⊗ᴶ-direct-definition ε δ q = refl

 ηᴶ : {X : 𝓤 ̇ } → X → J X
 ηᴶ = η (𝕁 R)

 extᴶ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → J Y) → J X → J Y
 extᴶ = ext (𝕁 R)

 mapᴶ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → J X → J Y
 mapᴶ = map (𝕁 R)

\end{code}

The following is the letter O for the contravariant outcome functor.

\begin{code}

module contravariant-functoriality-on-outcome-type
        (X : 𝓤 ̇ )
       where

 O : 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
 O R = functor (𝕁 R) X

 O-functor : {R : 𝓥 ̇ } {S : 𝓦 ̇ }
           → (S → R) → (O R → O S)
 O-functor f ε p = ε (f ∘ p)

 O-functor-id : {R : 𝓥 ̇ }
              → O-functor (𝑖𝑑 R) ＝ (𝑖𝑑 (O R))
 O-functor-id = refl

 O-functor-∘
  : {R : 𝓥 ̇ } {S : 𝓦 ̇ } {T : 𝓣 ̇ }
    (f : R → S) (g : S → T)
  → O-functor (g ∘ f) ＝ O-functor f ∘ O-functor g
 O-functor-∘ f g = refl

\end{code}
