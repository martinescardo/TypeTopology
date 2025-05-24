Taken from the Advanced Functional Programming module lecture notes 2023-24

Provides functions for manipulating isomorphisms

\begin{code}
{-# OPTIONS --without-K --safe #-}

module TGH.AFP2024.iso-utils where

open import MLTT.Spartan renaming (_+_ to _∔_ ; _∙_ to trans)
open import TGH.AFP2024.isomorphisms

open _≅_
open is-bijection

id-iso : (A : 𝓤₀ ̇) → A ≅ A
id-iso A = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : A → A
  f = id

  g : A → A
  g = id

  gf : g ∘ f ∼ id
  gf a = refl

  fg : f ∘ g ∼ id
  fg a = refl

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

≅-sym : {X Y : 𝓤₀ ̇} → X ≅ Y → Y ≅ X
≅-sym (Isomorphism f (Inverse g η ε)) = Isomorphism g (Inverse f ε η)

_∘ᵢ_ : {A B C : 𝓤₀ ̇} → B ≅ C → A ≅ B → A ≅ C
α ∘ᵢ β = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : _ → _
  f = bijection α ∘ bijection β

  g : _ → _
  g = inverse (bijectivity β) ∘ inverse (bijectivity α)

  gf : g ∘ f ∼ id
  gf a = trans (ap (inverse (bijectivity β)) (η (bijectivity α)
               (bijection β a)))
               (η (bijectivity β) a)

  fg : f ∘ g ∼ id
  fg c = trans (ap (bijection α) (ε (bijectivity β) (inverse
               (bijectivity α) c)))
               (ε (bijectivity α) c)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

-- Equational reasoning for iso's
_≅⟨_⟩_ : (X : 𝓤₀ ̇) {Y Z : 𝓤₀ ̇} → X ≅ Y → Y ≅ Z → X ≅ Z
X ≅⟨ p ⟩ q = q ∘ᵢ p

_∎ᵢ : (X : 𝓤₀ ̇) → X ≅ X
X ∎ᵢ = id-iso X

infixr  0 _≅⟨_⟩_
infix   1 _∎ᵢ

∔-unit-left-iso : (X : 𝓤₀ ̇) → X ≅ 𝟘 ∔ X
∔-unit-left-iso X = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : X → 𝟘 ∔ X
  f x = inr x

  g : 𝟘 ∔ X → X
  g (inl ())
  g (inr x) = x

  gf : g ∘ f ∼ id
  gf x = refl

  fg : f ∘ g ∼ id
  fg (inl ())
  fg (inr _) = refl

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
  
∔-pair-iso : {A B C D : 𝓤₀ ̇} → A ≅ B → C ≅ D → (A ∔ C) ≅ (B ∔ D)
∔-pair-iso {A} {B} {C} {D} α β
 = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : A ∔ C → B ∔ D
  f (inl a) = inl (bijection α a)
  f (inr c) = inr (bijection β c)

  g : B ∔ D → A ∔ C
  g (inl b) = inl (inverse (bijectivity α) b)
  g (inr d) = inr (inverse (bijectivity β) d)

  gf : g ∘ f ∼ id
  gf (inl a) = ap inl (η (bijectivity α) a)
  gf (inr c) = ap inr (η (bijectivity β) c)

  fg : f ∘ g ∼ id
  fg (inl b) = ap inl (ε (bijectivity α) b)
  fg (inr d) = ap inr (ε (bijectivity β) d)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

∔-assoc-iso : (A B C : 𝓤₀ ̇) → A ∔ B ∔ C ≅ (A ∔ B) ∔ C
∔-assoc-iso A B C = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : A ∔ B ∔ C → (A ∔ B) ∔ C
  f (inl a) = inl (inl a)
  f (inr (inl b)) = inl (inr b)
  f (inr (inr c)) = inr c

  g : (A ∔ B) ∔ C → A ∔ B ∔ C
  g (inl (inl a)) = inl a
  g (inl (inr b)) = inr (inl b)
  g (inr c) = inr (inr c)

  gf : g ∘ f ∼ id
  gf (inl a) = refl
  gf (inr (inl b)) = refl
  gf (inr (inr c)) = refl 

  fg : f ∘ g ∼ id
  fg (inl (inl a)) = refl
  fg (inl (inr b)) = refl
  fg (inr c) = refl

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

∔-left-swap-iso : (A B C : 𝓤₀ ̇) → A ∔ B ∔ C ≅ B ∔ A ∔ C
∔-left-swap-iso A B C = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : A ∔ B ∔ C → B ∔ A ∔ C
  f (inl a) = inr (inl a)
  f (inr (inl b)) = inl b
  f (inr (inr c)) = inr (inr c)

  g : B ∔ A ∔ C → A ∔ B ∔ C
  g (inl b) = inr (inl b)
  g (inr (inl a)) = inl a
  g (inr (inr c)) = inr (inr c)

  gf : g ∘ f ∼ id
  gf (inl a) = refl
  gf (inr (inl b)) = refl
  gf (inr (inr c)) = refl

  fg : f ∘ g ∼ id
  fg (inl b) = refl
  fg (inr (inl a)) = refl
  fg (inr (inr c)) = refl

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
