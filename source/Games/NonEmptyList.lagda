Martin Escardo, Paulo Oliva, 2024

Non-empty list monad.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module Games.NonEmptyList where

open import Games.Monad
open import MLTT.List renaming (map to lmap ; map-∘ to lmap-∘)
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

 lmap⁺ : {X Y : Type} (f : X → Y) (xs : List⁺ X) → List⁺ Y
 lmap⁺ f xs = lmap f (ι xs) ,
              map-is-non-empty f (ι xs) (underlying-list⁺-is-non-empty xs)

 concat⁺-non-empty : {X : Type} (xss : List⁺ (List⁺ X))
                   → is-non-empty (concat (lmap ι (ι xss)))
 concat⁺-non-empty (((xs , xs-ne) ∷ xss) , xss-ne) =
  is-non-empty-++ xs (concat (lmap ι xss)) xs-ne

 concat⁺ : {X : Type} → List⁺ (List⁺ X) → List⁺ X
 concat⁺ {X} xss = concat (lmap ι (ι xss)) , concat⁺-non-empty xss

 mapᴸ⁺-lemma : {X Y : Type} (f : X → Y) (xs : List⁺ X)
             → mapᴸ⁺ f xs ＝ lmap⁺ f xs
 mapᴸ⁺-lemma f xs = to-List⁺-＝ (concat-singletons' f (ι xs))

 extᴸ⁺-explicitly : {X Y : Type}
                    (f : X → List⁺ Y)
                    (xs : List⁺ X)
                  → extᴸ⁺ f xs ＝ concat⁺ (lmap⁺ f xs)
 extᴸ⁺-explicitly f xs = to-List⁺-＝ I
  where
   I : concat (lmap (ι ∘ f) (ι xs)) ＝ concat (lmap ι (lmap f (ι xs)))
   I = ap concat (lmap-∘ f ι (ι xs))

 open import UF.FunExt

 ⊗ᴸ⁺-explicitly
  : funext₀
  → {X : Type} {Y : X → Type}
    (xs : List⁺ X)
    (ys : (x : X) → List⁺ (Y x))
  → xs ⊗ᴸ⁺ ys ＝ concat⁺ (lmap⁺ (λ x → lmap⁺ (λ y → x , y) (ys x)) xs)
 ⊗ᴸ⁺-explicitly fe xs ys =
  xs ⊗ᴸ⁺ ys ＝⟨ refl ⟩
  extᴸ⁺ (λ x → mapᴸ⁺ (λ y → x , y) (ys x)) xs           ＝⟨ I ⟩
  extᴸ⁺ (λ x → lmap⁺ (λ y → x , y) (ys x)) xs           ＝⟨ II ⟩
  concat⁺ (lmap⁺ (λ x → lmap⁺ (λ y → x , y) (ys x)) xs) ∎
   where
    I  = ap (λ - → extᴸ⁺ - xs)
            (dfunext fe (λ x → mapᴸ⁺-lemma (λ y → x , y) (ys x)))
    II = extᴸ⁺-explicitly (λ x → lmap⁺ (λ y → x , y) (ys x)) xs

 _+++_ : {X : Type} → List⁺ X → List X → List⁺ X
 (xs , xs-ne) +++ ys = (xs ++ ys) , is-non-empty-++ xs ys xs-ne

 head⁺-of-+++ : {X : Type} (xs : List⁺ X) (ys : List X)
              → head⁺ (xs +++ ys) ＝ head⁺ xs
 head⁺-of-+++ ((x ∷ xs) , xs-ne) ys = refl

 head⁺-of-concat⁺ : {X : Type} (xss : List⁺ (List⁺ X))
                  → head⁺ (concat⁺ xss) ＝ head⁺ (head⁺ xss)
 head⁺-of-concat⁺ ((xs ∷ xss) , cons-is-non-empty) = head⁺-of-+++ xs (concat (lmap ι xss))

 head⁺-of-lmap⁺ :  {X Y : Type} (f : X → Y) (xs : List⁺ X)
                → head⁺ (lmap⁺ f xs) ＝ f (head⁺ xs)
 head⁺-of-lmap⁺ f ((x ∷ xs) , _) = refl
