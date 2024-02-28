[⇐ Index](../html/TWA.Thesis.index.html)

# Orders

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.DiscreteAndSeparated
open import UF.Subsingletons
open import UF.PropTrunc
open import Quotient.Type
 using (is-prop-valued;is-equiv-relation;EqRel)
open import Notation.Order
open import Naturals.Order

module TWA.Thesis.Chapter4.ApproxOrder (fe : FunExt) where

open import TWA.Thesis.Chapter3.ClosenessSpaces fe
```

## Traditional orders

```
is-preorder : {X : 𝓤  ̇ } → (X → X → 𝓦  ̇ ) → 𝓤 ⊔ 𝓦  ̇ 
is-preorder _≤_ = reflexive _≤_
                × transitive _≤_
                × is-prop-valued _≤_

is-partial-order : {X : 𝓤  ̇ } → (X → X → 𝓦  ̇ ) → 𝓤 ⊔ 𝓦  ̇
is-partial-order {_} {_} {X} _≤_
 = is-preorder _≤_ × antisymmetric _≤_

linear :  {X : 𝓤  ̇ } → (X → X → 𝓦  ̇ ) → 𝓤 ⊔ 𝓦  ̇
linear {_} {_} {X} _≤_ = (x y : X) → (x ≤ y) + (y ≤ x)

is-linear-preorder : {X : 𝓤  ̇ } → (X → X → 𝓦  ̇ ) → 𝓤 ⊔ 𝓦  ̇
is-linear-preorder {_} {_} {X} _≤_
 = is-preorder _≤_ × linear _≤_

is-linear-order : {X : 𝓤  ̇ } → (X → X → 𝓦  ̇ ) → 𝓤 ⊔ 𝓦  ̇
is-linear-order {_} {_} {X} _≤_
 = is-partial-order _≤_ × linear _≤_

discrete-reflexive-antisym-linear-order-is-decidable
 : {X : 𝓤  ̇ } 
 → is-discrete X
 → (_≤_ : X → X → 𝓦  ̇ )
 → reflexive _≤_
 → antisymmetric _≤_
 → linear _≤_
 → (x y : X)
 → is-decidable (x ≤ y)
discrete-reflexive-antisym-linear-order-is-decidable
 ds _≤_ r a l x y
 = Cases (ds x y) (λ x=y → inl (transport (x ≤_) x=y (r x)))
    (λ x≠y → Cases (l x y) inl
               (inr ∘ (λ y≤x x≤y → x≠y (a x y x≤y y≤x))))

```

## Approximate orders

```
is-approx-order : (X : ClosenessSpace 𝓤)
                → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ )
                → 𝓤 ⊔ 𝓦'  ̇
is-approx-order X _≤ⁿ_
 = ((ϵ : ℕ) → is-linear-preorder (λ x y → (x ≤ⁿ y) ϵ))
 × ((ϵ : ℕ) (x y : ⟨ X ⟩) → is-decidable ((x ≤ⁿ y) ϵ))
 × ((ϵ : ℕ) (x y : ⟨ X ⟩) →   C X ϵ x y → (x ≤ⁿ y) ϵ)
 
≤-refl⟨_⟩
 : {X : 𝓤 ̇ } {_≤_ : X → X → 𝓦 ̇ }
 → is-preorder _≤_
 → reflexive _≤_
≤-refl⟨ r , t , p ⟩ = r

≤-trans⟨_⟩
 : {X : 𝓤 ̇ } {_≤_ : X → X → 𝓦 ̇ }
 → is-preorder _≤_
 → transitive _≤_
≤-trans⟨ r , t , p ⟩ = t

≤-prop⟨_⟩
 : {X : 𝓤 ̇ } {_≤_ : X → X → 𝓦 ̇ }
 → is-preorder _≤_
 → is-prop-valued _≤_
≤-prop⟨ r , t , p ⟩ = p

≤-pre⟨_⟩
 : {X : 𝓤 ̇ } {_≤_ : X → X → 𝓦 ̇ }
 → is-linear-preorder _≤_
 → is-preorder _≤_
≤-pre⟨ pre , l ⟩ = pre

≤-linear⟨_⟩
 : {X : 𝓤 ̇ } {_≤_ : X → X → 𝓦 ̇ }
 → is-linear-preorder _≤_
 → (x y : X) → (x ≤ y) + (y ≤ x)
≤-linear⟨ pre , l ⟩ = l

≤ⁿ-all-linear
 : (X : ClosenessSpace 𝓤)
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤ⁿ_
 → (ϵ : ℕ) → is-linear-preorder (λ x y → (x ≤ⁿ y) ϵ)
≤ⁿ-all-linear X (l , d , c) = l

≤ⁿ-refl
 : (X : ClosenessSpace 𝓤)
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤ⁿ_
 → (ϵ : ℕ)
 → (x : ⟨ X ⟩) → (x ≤ⁿ x) ϵ
≤ⁿ-refl X (l , d , c) ϵ = (pr₁ ∘ pr₁) (l ϵ)

≤ⁿ-trans
 : (X : ClosenessSpace 𝓤)
 → {_≤ⁿ_  : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦 ̇ }
 → is-approx-order X _≤ⁿ_
 → (ϵ : ℕ) (x y z : ⟨ X ⟩)
 → (x ≤ⁿ y) ϵ → (y ≤ⁿ z) ϵ → (x ≤ⁿ z) ϵ
≤ⁿ-trans X (l , d , c) ϵ = (pr₁ ∘ pr₂ ∘ pr₁) (l ϵ)

≤ⁿ-prop
 : (X : ClosenessSpace 𝓤)
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤ⁿ_
 → (ϵ : ℕ) (x y : ⟨ X ⟩)
 → is-prop ((x ≤ⁿ y) ϵ)
≤ⁿ-prop X (l , d , c) ϵ = (pr₂ ∘ pr₂ ∘ pr₁) (l ϵ)

≤ⁿ-linear
 : (X : ClosenessSpace 𝓤)
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤ⁿ_
 → (ϵ : ℕ) (x y : ⟨ X ⟩)
 → (x ≤ⁿ y) ϵ + (y ≤ⁿ x) ϵ
≤ⁿ-linear X (l , d , c) ϵ = pr₂ (l ϵ)

≤ⁿ-decidable
 : (X : ClosenessSpace 𝓤)
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤ⁿ_
 → (ϵ : ℕ) (x y : ⟨ X ⟩)
 → is-decidable ((x ≤ⁿ y) ϵ)
≤ⁿ-decidable X (l , d , c) = d

≤ⁿ-close
 : (X : ClosenessSpace 𝓤)
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤ⁿ_
 → (ϵ : ℕ) (x y : ⟨ X ⟩)
 → C X ϵ x y → (x ≤ⁿ y) ϵ
≤ⁿ-close X (l , d , c) = c

module ApproxOrder-Relates (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 _relates-to→_ : {X : 𝓤 ̇ }
               → (_≤ⁿ_ : X → X → ℕ → 𝓦'  ̇ )
               → (_≤_  : X → X → 𝓦 ̇ )
               → 𝓤 ⊔ 𝓦 ⊔ 𝓦'  ̇
 _≤ⁿx_ relates-to→ _≤x_ 
  = ∀ x y → ((n : ℕ) → (x ≤ⁿx y) n) → x ≤x y

 _relates-to←_ : {X : 𝓤 ̇ }
               → (_≤ⁿ_ : X → X → ℕ → 𝓦'  ̇ )
               → (_≤_  : X → X → 𝓦 ̇ )
               → 𝓤 ⊔ 𝓦 ⊔ 𝓦'  ̇
 _≤ⁿx_ relates-to← _≤x_
  = ∀ x y → x ≤x y → ∃ n ꞉ ℕ , ((ϵ : ℕ) → n ≤ ϵ → (x ≤ⁿx y) ϵ)
  
 approx-order-relates : (X : ClosenessSpace 𝓤)
                      → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ )
                      → is-approx-order X _≤ⁿ_
                      → (_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
                      → is-preorder _≤_
                      → 𝓤 ⊔ 𝓦 ⊔ 𝓦'  ̇
 approx-order-relates X _≤ⁿ_ _ _≤_ _
  = _≤ⁿ_ relates-to→ _≤_
  × _≤ⁿ_ relates-to← _≤_
```

## Predicates from approximate orders

```
approx-order-ucontinuous-l
 : (X : ClosenessSpace 𝓤)
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → (a : is-approx-order X _≤ⁿ_)
 → (ε : ℕ) (y : ⟨ X ⟩)
 → p-ucontinuous X (λ x → (x ≤ⁿ y) ε , ≤ⁿ-prop X a ε x y)
approx-order-ucontinuous-l X a ε y
 = ε , (λ x₁ x₂ Cx₁x₂ x₁≤ⁿy
        → ≤ⁿ-trans X a ε x₂ x₁ y
            (≤ⁿ-close X a ε x₂ x₁ (C-sym X ε x₁ x₂ Cx₁x₂))
            x₁≤ⁿy)

approx-order-ucontinuous-r
 : (X : ClosenessSpace 𝓤)
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → (a : is-approx-order X _≤ⁿ_)
 → (ε : ℕ) (y : ⟨ X ⟩)
 → p-ucontinuous X (λ x → (y ≤ⁿ x) ε , ≤ⁿ-prop X a ε y x)
approx-order-ucontinuous-r X a ε y
 = ε , (λ x₁ x₂ Cx₁x₂ x₁≤ⁿy
        → ≤ⁿ-trans X a ε y x₁ x₂
            x₁≤ⁿy
            (≤ⁿ-close X a ε x₁ x₂ Cx₁x₂))

-- LINK: approx-order-uc-predicate
approx-order-uc-predicate-l : (X : ClosenessSpace 𝓤)
                            → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦 ̇ )
                            → is-approx-order X _≤ⁿ_
                            → (ϵ : ℕ) (y : ⟨ X ⟩)
                            → decidable-uc-predicate 𝓦 X
approx-order-uc-predicate-l X _≤ⁿ_ a ϵ y
 = ((λ x → (x ≤ⁿ y) ϵ , ≤ⁿ-prop X a ϵ x y)
 , λ x → ≤ⁿ-decidable X a ϵ x y)
 , approx-order-ucontinuous-l X a ϵ y

approx-order-uc-predicate-r : (X : ClosenessSpace 𝓤)
                            → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦 ̇ )
                            → is-approx-order X _≤ⁿ_
                            → (ϵ : ℕ) (y : ⟨ X ⟩)
                            → decidable-uc-predicate 𝓦 X
approx-order-uc-predicate-r X _≤ⁿ_ a ϵ y
 = ((λ x → (y ≤ⁿ x) ϵ , ≤ⁿ-prop X a ϵ y x)
 , λ x → ≤ⁿ-decidable X a ϵ y x)
 , approx-order-ucontinuous-r X a ϵ y

approx-order-f-uc-predicate-l : (X : ClosenessSpace 𝓤)
                              → (Y : ClosenessSpace 𝓥)
                              → (f : ⟨ X ⟩ → ⟨ Y ⟩)
                              → f-ucontinuous X Y f
                              → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦 ̇ )
                              → is-approx-order Y _≤ⁿ_
                              → (ϵ : ℕ) (y : ⟨ Y ⟩)
                              → decidable-uc-predicate 𝓦 X
approx-order-f-uc-predicate-l X Y f ϕ _≤ⁿ_ a ϵ y
 = ((λ x → (f x ≤ⁿ y) ϵ , ≤ⁿ-prop Y a ϵ (f x) y)
 , (λ x → ≤ⁿ-decidable Y a ϵ (f x) y))
 , p-ucontinuous-comp X Y f ϕ
     (λ x → (x ≤ⁿ y) ϵ , ≤ⁿ-prop Y a ϵ x y)
     (approx-order-ucontinuous-l Y a ϵ y)

approx-order-f-uc-predicate-r : (X : ClosenessSpace 𝓤)
                              → (Y : ClosenessSpace 𝓥)
                              → (f : ⟨ X ⟩ → ⟨ Y ⟩)
                              → f-ucontinuous X Y f
                              → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦 ̇ )
                              → is-approx-order Y _≤ⁿ_
                              → (ϵ : ℕ) (y : ⟨ Y ⟩)
                              → decidable-uc-predicate 𝓦 X
approx-order-f-uc-predicate-r X Y f ϕ _≤ⁿ_ a ϵ y
 = ((λ x → (y ≤ⁿ f x) ϵ , ≤ⁿ-prop Y a ϵ y (f x))
 , (λ x → ≤ⁿ-decidable Y a ϵ y (f x)))
 , p-ucontinuous-comp X Y f ϕ
     (λ x → (y ≤ⁿ x) ϵ , ≤ⁿ-prop Y a ϵ y x)
     (approx-order-ucontinuous-r Y a ϵ y)
```

[⇐ Index](../html/TWA.Thesis.index.html)
