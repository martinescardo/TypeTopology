Martin Escardo, Paulo Oliva, 2024

Non-empty list monad.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module MonadOnTypes.NonEmptyList where

open import MonadOnTypes.Construction
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

head⁺-is-member : {X : Type} (xs : List⁺ X)
                → member (head⁺ xs) (ι xs)
head⁺-is-member ((x ∷ xs) , _) = in-head

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
    (yf : (x : X) → List⁺ (Y x))
  → xs ⊗ᴸ⁺ yf ＝ concat⁺ (lmap⁺ (λ x → lmap⁺ (λ y → x , y) (yf x)) xs)
 ⊗ᴸ⁺-explicitly fe xs yf =
  xs ⊗ᴸ⁺ yf ＝⟨refl⟩
  extᴸ⁺ (λ x → mapᴸ⁺ (λ y → x , y) (yf x)) xs           ＝⟨ I ⟩
  extᴸ⁺ (λ x → lmap⁺ (λ y → x , y) (yf x)) xs           ＝⟨ II ⟩
  concat⁺ (lmap⁺ (λ x → lmap⁺ (λ y → x , y) (yf x)) xs) ∎
   where
    I  = ap (λ - → extᴸ⁺ - xs)
            (dfunext fe (λ x → mapᴸ⁺-lemma (λ y → x , y) (yf x)))
    II = extᴸ⁺-explicitly (λ x → lmap⁺ (λ y → x , y) (yf x)) xs

 ι-⊗ᴸ⁺-explicitly
  : funext₀
  → {X : Type} {Y : X → Type}
    (xs : List⁺ X)
    (ys : (x : X) → List⁺ (Y x))
  → ι (xs ⊗ᴸ⁺ ys) ＝ concat (lmap (λ x → lmap (x ,_) (ι (ys x))) (ι xs))
 ι-⊗ᴸ⁺-explicitly fe xs ys =
   ι (xs ⊗ᴸ⁺ ys)                                             ＝⟨ I ⟩
   ι (concat⁺ (lmap⁺ (λ x → lmap⁺ (λ y → x , y) (ys x)) xs)) ＝⟨refl⟩
   concat (lmap ι (lmap (λ x → lmap⁺ (x ,_) (ys x)) (ι xs))) ＝⟨ II ⟩
   concat (lmap (λ x → lmap (x ,_) (ι (ys x))) (ι xs))       ∎
    where
     I  = ap ι (⊗ᴸ⁺-explicitly fe xs ys)
     II = ap concat ((lmap-∘ (λ x → lmap⁺ (x ,_) (ys x)) ι (ι xs))⁻¹)

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

 split-membership : funext₀
                  → {X : Type}
                    {Y : X → Type}
                    (x : X)
                    (y : Y x)
                    (xs : List⁺ X)
                    (yf : (x : X) → List⁺ (Y x))
                  → member (x , y) (ι (xs ⊗ᴸ⁺ yf))
                  → member x (ι xs) × member y (ι (yf x))
 split-membership fe {X} {Y} x y xs yf m = m₀ , m₁
  where
   f : X → List (Σ x ꞉ X , Y x)
   f x = lmap (x ,_) (ι (yf x))

   I : ι (xs ⊗ᴸ⁺ yf) ＝ concat (lmap f (ι xs))
   I = ι-⊗ᴸ⁺-explicitly fe xs yf

   II : member (x , y) (concat (lmap f (ι xs)))
   II = transport (member (x , y)) I m

   III : Σ zs ꞉ List (Σ x ꞉ X , Y x)
             , member zs (lmap f (ι xs))
             × member (x , y) zs
   III = member-of-concat←
          (x , y)
          (lmap f (ι xs))
          II

   zs : List (Σ x ꞉ X , Y x)
   zs = pr₁ III

   III₀ : member zs (lmap f (ι xs))
   III₀ = pr₁ (pr₂ III)

   III₁ : member (x , y) zs
   III₁ = pr₂ (pr₂ III)

   IV : Σ x' ꞉ X , member x' (ι xs) × (lmap (x' ,_) (ι (yf x')) ＝ zs)
   IV = member-of-map← f zs (ι xs) III₀

   x' : X
   x' = pr₁ IV

   IV₀ : member x' (ι xs)
   IV₀ = pr₁ (pr₂ IV)

   IV₁ : lmap (x' ,_) (ι (yf x')) ＝ zs
   IV₁ = pr₂ (pr₂ IV)

   V : member (x , y) (lmap (x' ,_) (ι (yf x')))
   V = transport⁻¹ (member (x , y)) IV₁ III₁

   VI : Σ y' ꞉ Y x' , member y' (ι (yf x')) × ((x' , y') ＝ (x , y))
   VI = member-of-map← (x' ,_) (x , y) (ι (yf x')) V

   y' : Y x'
   y' = pr₁ VI

   VI₀ : member y' (ι (yf x'))
   VI₀ = pr₁ (pr₂ VI)

   VI₁ : (x' , y') ＝ (x , y)
   VI₁ = pr₂ (pr₂ VI)

   m₀ : member x (ι xs)
   m₀ = transport (λ - → member - (ι xs)) (ap pr₁ VI₁) IV₀

   VII : ∀ x' y' x y → (x' , y') ＝ (x , y) →  member y' (ι (yf x')) → member y (ι (yf x))
   VII x' y' x y refl = id

   m₁ : member y (ι (yf x))
   m₁ = VII x' y' x y VI₁ VI₀

 join-membership : funext₀
                 → {X : Type}
                   {Y : X → Type}
                   (x : X)
                   (y : Y x)
                   (xs : List⁺ X)
                   (yf : (x : X) → List⁺ (Y x))
                 → member x (ι xs) × member y (ι (yf x))
                 → member (x , y) (ι (xs ⊗ᴸ⁺ yf))
 join-membership fe {X} {Y} x y xs yf (m₀ , m₁) = m
  where
   f : X → List (Σ x ꞉ X , Y x)
   f x = lmap (x ,_) (ι (yf x))

   I : ι (xs ⊗ᴸ⁺ yf) ＝ concat (lmap f (ι xs))
   I = ι-⊗ᴸ⁺-explicitly fe xs yf

   II : member (x , y) (f x)
   II = member-of-map→ (x ,_) (ι (yf x)) y m₁

   III : member (f x) (lmap f (ι xs))
   III = member-of-map→ f (ι xs) x m₀

   IV : member (x , y) (concat (lmap f (ι xs)))
   IV = member-of-concat→ (x , y) (lmap f (ι xs)) (f x) III II

   m : member (x , y) (ι (xs ⊗ᴸ⁺ yf))
   m = transport (member (x , y)) (I ⁻¹) IV

\end{code}
