[⇐ Index](../html/TWA.Thesis.index.html)

# Equality of uniformly continuous predicates

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import NotionsOfDecidability.Complemented
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

module TWA.Thesis.Chapter3.PredicateEquality
  (fe : FunExt) (pe : PropExt) where

open import TWA.Thesis.Chapter3.SearchableTypes fe
 hiding (decidable-predicate;decidable-uc-predicate)
open import TWA.Thesis.Chapter3.ClosenessSpaces fe

predicate-＝ : {X : 𝓤 ̇ }
             → (p₁ p₂ : X → Ω 𝓦)
             → ((x : X) → p₁ x holds ↔ p₂ x holds)
             → p₁ ＝ p₂
predicate-＝ p₁ p₂ f
 = dfunext (fe _ _)
     (λ x → to-subtype-＝ (λ _ → being-prop-is-prop (fe _ _))
       (pe _ (pr₂ (p₁ x)) (pr₂ (p₂ x)) (pr₁ (f x)) (pr₂ (f x))))

complemented-is-prop : {X : 𝓤 ̇ }
                     → (p : X → Ω 𝓦)
                     → is-prop (is-complemented (λ x → p x holds))
complemented-is-prop p
 = Π-is-prop (fe _ _) (λ x → +-is-prop (pr₂ (p x))
     (Π-is-prop (fe _ _) (λ _ → 𝟘-is-prop))
     (λ px ¬px → ¬px px))

uc-continuous-is-prop : (X : ClosenessSpace 𝓤)
                      → (p : ⟨ X ⟩ → Ω 𝓦)
                      → (δ : ℕ)
                      → is-prop (p-ucontinuous-with-mod X p δ)
uc-continuous-is-prop X p δ
 = Π-is-prop (fe _ _) (λ _ → Π-is-prop (fe _ _)
     (λ _ → Π-is-prop (fe _ _) (λ _ → Π-is-prop (fe _ _)
       (λ _ → pr₂ (p _)))))

decidable-uc-predicate-＝''
 : (X : ClosenessSpace 𝓤)
 → (δ : ℕ)
 → (p₁ p₂ : ⟨ X ⟩ → Ω 𝓦)
 → (d₁ : is-complemented (λ x → p₁ x holds))
 → (d₂ : is-complemented (λ x → p₂ x holds))
 → (ϕ₁ : p-ucontinuous-with-mod X p₁ δ)
 → (ϕ₂ : p-ucontinuous-with-mod X p₂ δ)
 → p₁ ＝ p₂
 → _＝_ {_} {decidable-uc-predicate 𝓦 X}
     ((p₁ , d₁) , δ , ϕ₁) ((p₂ , d₂) , δ , ϕ₂)
decidable-uc-predicate-＝'' X δ p p d₁ d₂ ϕ₁ ϕ₂ refl
 = ap (λ - → (p , -) , δ , ϕ₁) (complemented-is-prop p d₁ d₂)
 ∙ ap (λ - → (p , d₂) , δ , -) (uc-continuous-is-prop X p δ ϕ₁ ϕ₂)

decidable-uc-predicate-＝'
 : (X : ClosenessSpace 𝓤)
 → (δ : ℕ)
 → (p₁ p₂ : ⟨ X ⟩ → Ω 𝓦)
 → (d₁ : is-complemented (λ x → p₁ x holds))
 → (d₂ : is-complemented (λ x → p₂ x holds))
 → (ϕ₁ : p-ucontinuous-with-mod X p₁ δ)
 → (ϕ₂ : p-ucontinuous-with-mod X p₂ δ)
 → ((x : ⟨ X ⟩) → p₁ x holds ↔ p₂ x holds)
 → _＝_ {_} {decidable-uc-predicate 𝓦 X}
     ((p₁ , d₁) , δ , ϕ₁) ((p₂ , d₂) , δ , ϕ₂)
decidable-uc-predicate-＝' X δ p₁ p₂ d₁ d₂ ϕ₁ ϕ₂ f
 = decidable-uc-predicate-＝'' X δ p₁ p₂ d₁ d₂ ϕ₁ ϕ₂
     (predicate-＝ p₁ p₂ f)

decidable-uc-predicate-＝
 : (X : ClosenessSpace 𝓤)
 → (p@((p₁ , d₁) , δ₁ , ϕ₁) q@((p₂ , d₂) , δ₂ , ϕ₂)
    : decidable-uc-predicate 𝓦 X)
 → δ₁ ＝ δ₂
 → ((x : ⟨ X ⟩) → p₁ x holds ↔ p₂ x holds)
 → p ＝ q
decidable-uc-predicate-＝
 X ((p₁ , d₁) , δ , ϕ₁) ((p₂ , d₂) , δ , ϕ₂) refl f
 = decidable-uc-predicate-＝' X δ p₁ p₂ d₁ d₂ ϕ₁ ϕ₂ f

decidable-uc-predicate-with-mod-＝
 : (X : ClosenessSpace 𝓤)
 → (δ : ℕ)
 → (p@((p₁ , d₁) , ϕ₁) q@((p₂ , d₂) , ϕ₂)
    : decidable-uc-predicate-with-mod 𝓦 X δ)
 → ((x : ⟨ X ⟩) → p₁ x holds ↔ p₂ x holds)
 → p ＝ q
decidable-uc-predicate-with-mod-＝
 X δ ((p₁ , d₁) , ϕ₁) ((p₂ , d₂) , ϕ₂) f
 = to-subtype-＝ (λ p → uc-continuous-is-prop X (pr₁ p) δ)
     (to-subtype-＝ (λ p → complemented-is-prop p)
       (predicate-＝ p₁ p₂ f))
```

[⇐ Index](../html/TWA.Thesis.index.html)
