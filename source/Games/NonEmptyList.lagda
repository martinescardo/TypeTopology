Martin Escardo, Paulo Oliva, 2024

Non-empty list monad.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module Games.NonEmptyList where

open import Games.Monad
open import MLTT.List hiding (map)
open import Notation.CanonicalMap
open import UF.Subsingletons

being-non-empty-is-prop : {X : 𝓤 ̇ } (xs : List X) → is-prop (is-non-empty xs)
being-non-empty-is-prop []       = 𝟘-is-prop
being-non-empty-is-prop (x ∷ xs) = 𝟙-is-prop

List⁺ : Type → Type
List⁺ X = Σ xs ꞉ List X , is-non-empty xs

module _ {X : Type} where

 [_]⁺ : X → List⁺ X
 [ x ]⁺ = (x ∷ []) , cons-is-non-empty

 head⁺ : List⁺ X → X
 head⁺ ((x ∷ xs) , cons-is-non-empty) = x

 tail⁺ : List⁺ X → List X
 tail⁺ ((x ∷ xs) , cons-is-non-empty) = xs

 cons⁺ : X → List X → List⁺ X
 cons⁺ x xs = (x ∷ xs) , cons-is-non-empty

 underlying-list⁺ : List⁺ X → List X
 underlying-list⁺ = pr₁

 underlying-list⁺-is-non-empty : (xs : List⁺ X)
                               → is-non-empty (underlying-list⁺ xs)
 underlying-list⁺-is-non-empty = pr₂

 instance
  canonical-map-List⁺-to-List : Canonical-Map (List⁺ X) (List X)
  ι {{canonical-map-List⁺-to-List}} = underlying-list⁺

 to-List⁺-＝ : {xs ys : List⁺ X} → ι xs ＝ ι ys → xs ＝ ys
 to-List⁺-＝ = to-subtype-＝ being-non-empty-is-prop

List-ext-lemma⁻ : {X Y : Type} (f : X → List⁺ Y) (xs : List X)
                → is-non-empty xs
                → is-non-empty (List-ext (ι ∘ f) xs)
List-ext-lemma⁻ f (x ∷ xs) cons-is-non-empty =
 is-non-empty-++ (ι (f x)) _ (underlying-list⁺-is-non-empty (f x))

𝕃⁺ : Monad
𝕃⁺ = record {
 functor = List⁺ ;
 η       = λ x → (x ∷ []) , cons-is-non-empty ;
 ext     = λ {X} {Y} (f : X → List⁺ Y) (xs : List⁺ X)
            → List-ext (ι ∘ f) (ι xs) ,
              List-ext-lemma⁻ f (ι xs) (underlying-list⁺-is-non-empty xs) ;
 ext-η   = λ {X} (xs : List⁺ X)
            → to-List⁺-＝ (concat-singletons (ι xs)) ;
 unit    = λ {X} {Y} (f : X → List⁺ Y) (x : X)
            → to-List⁺-＝ (List-ext-unit (ι ∘ f) x) ;
 assoc   = λ {X} {Y} {Z} (g : Y → List⁺ Z) (f : X → List⁺ Y) (xs : List⁺ X)
            → to-List⁺-＝ (List-ext-assoc (ι ∘ g) (ι ∘ f) (ι xs))
 }

module List⁺-definitions where

 _⊗ᴸ⁺_ : {X : Type} {Y : X → Type}
      → List⁺ X
      → ((x : X) → List⁺ (Y x))
      → List⁺ (Σ x ꞉ X , Y x)
 _⊗ᴸ⁺_ = _⊗_ 𝕃⁺

 ηᴸ⁺ : {X : Type} → X → List⁺ X
 ηᴸ⁺ = η 𝕃⁺

 extᴸ⁺ : {X Y : Type} → (X → List⁺ Y) → List⁺ X → List⁺ Y
 extᴸ⁺ = ext 𝕃⁺

 mapᴸ⁺ : {X Y : Type} → (X → Y) → List⁺ X → List⁺ Y
 mapᴸ⁺ = map 𝕃⁺
