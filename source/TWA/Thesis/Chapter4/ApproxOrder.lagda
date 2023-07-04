\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Quotient
open import UF.Subsingletons

module TWA.Thesis.Chapter4.ApproxOrder (fe : FunExt) where

open import TWA.Thesis.Chapter3.ClosenessSpaces fe

is-preorder : {X : 𝓤  ̇ } → (X → X → 𝓦  ̇ ) → 𝓤 ⊔ 𝓦  ̇ 
is-preorder _≤_ = reflexive _≤_
                × transitive _≤_
                × is-prop-valued _≤_

linear :  {X : 𝓤  ̇ } → (X → X → 𝓦  ̇ ) → 𝓤 ⊔ 𝓦  ̇
linear {_} {_} {X} _≤_ = (x y : X) → (x ≤ y) + (y ≤ x)

is-linear-order : {X : 𝓤  ̇ } → (X → X → 𝓦  ̇ ) → 𝓤 ⊔ 𝓦  ̇
is-linear-order {_} {_} {X} _≤_ = is-preorder _≤_ × linear _≤_

is-strict-order : {X : 𝓤  ̇ } → (X → X → 𝓦  ̇ ) → 𝓤 ⊔ 𝓦  ̇ 
is-strict-order {_} {_} {X} _<_
 = ((x : X) → ¬ (x < x))
 × transitive _<_
 × ((x y : X) → x < y → ¬ (y < x))
 × is-prop-valued _<_

trichotomous : {X : 𝓤 ̇ } → (_<_ : X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
trichotomous {𝓤} {𝓥} {X} _<_ = (x y : X) → (x < y) + (x ＝ y) + (y < x)

is-strict-linear-order : {X : 𝓤  ̇ } → (X → X → 𝓦  ̇ ) → 𝓤 ⊔ 𝓦  ̇ 
is-strict-linear-order {_} {_} {X} _<_
 = is-strict-order _<_ × trichotomous _<_

strict-trichotomous-order-decidable : {X : 𝓤  ̇ }
                                    → (_<'_ : X → X → 𝓦  ̇ )
                                    → is-strict-order _<'_
                                    → trichotomous _<'_
                                    → (x y : X)
                                    → is-decidable (x <' y)
strict-trichotomous-order-decidable _<'_ (i , t , a , p) tri x y
 = Cases (tri x y) inl
  (cases (λ x＝y → inr (transport (λ - → ¬ (x <' -)) x＝y (i x)))
         (inr ∘ a y x))

is-approx-order : (X : ClosenessSpace 𝓤)
                → (_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
                → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ )
                → 𝓤 ⊔ 𝓦 ⊔ 𝓦'  ̇
is-approx-order X _≤_ _≤ⁿ_
 = is-preorder _≤_
 × ((ϵ : ℕ) → is-linear-order (λ x y → (x ≤ⁿ y) ϵ))
 × ((ϵ : ℕ) (x y : ⟨ X ⟩) → is-decidable ((x ≤ⁿ y) ϵ))
 × ((ϵ : ℕ) (x y : ⟨ X ⟩) →   C X ϵ x y → (x ≤ⁿ y) ϵ)
 × ((ϵ : ℕ) (x y : ⟨ X ⟩) → ¬ C X ϵ x y → (x ≤ⁿ y) ϵ ⇔ x ≤ y)

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
 → is-linear-order _≤_
 → is-preorder _≤_
≤-pre⟨ pre , l ⟩ = pre

≤-linear⟨_⟩
 : {X : 𝓤 ̇ } {_≤_ : X → X → 𝓦 ̇ }
 → is-linear-order _≤_
 → (x y : X) → (x ≤ y) + (y ≤ x)
≤-linear⟨ pre , l ⟩ = l

<-irref⟨_⟩
 : {X : 𝓤 ̇ } {_<_ : X → X → 𝓦 ̇ }
 → is-strict-order _<_
 → (x : X) → ¬ (x < x)
<-irref⟨ i , t , a , p ⟩ = i

<-trans⟨_⟩
 : {X : 𝓤 ̇ } {_<_ : X → X → 𝓦 ̇ }
 → is-strict-order _<_
 → transitive _<_
<-trans⟨ i , t , a , p ⟩ = t

<-anti⟨_⟩
 : {X : 𝓤 ̇ } {_<_ : X → X → 𝓦 ̇ }
 → is-strict-order _<_
 → (x y : X) → x < y → ¬ (y < x)
<-anti⟨ i , t , a , p ⟩ = a

<-prop⟨_⟩
 : {X : 𝓤 ̇ } {_<_ : X → X → 𝓦 ̇ }
 → is-strict-order _<_
 → is-prop-valued _<_
<-prop⟨ i , t , a , p ⟩ = p

<-strict⟨_⟩
 : {X : 𝓤 ̇ } {_<_ : X → X → 𝓦 ̇ }
 → is-strict-linear-order _<_
 → is-strict-order _<_
<-strict⟨ str , t ⟩ = str

<-trich⟨_⟩ : {X : 𝓤 ̇ } {_<_ : X → X → 𝓦 ̇ }
 → is-strict-linear-order _<_
 → trichotomous _<_
<-trich⟨ str , t ⟩ = t

≤ⁿ-pre
 : (X : ClosenessSpace 𝓤)
 → {_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ }
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤_ _≤ⁿ_
 → is-preorder _≤_
≤ⁿ-pre X (p , l , d , c , a) = p

≤ⁿ-all-linear
 : (X : ClosenessSpace 𝓤)
 → {_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ }
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤_ _≤ⁿ_
 → (ϵ : ℕ) → is-linear-order (λ x y → (x ≤ⁿ y) ϵ)
≤ⁿ-all-linear X (p , l , d , c , a) = l

≤ⁿ-refl
 : (X : ClosenessSpace 𝓤)
 → {_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ }
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤_ _≤ⁿ_
 → (ϵ : ℕ)
 → (x : ⟨ X ⟩) → (x ≤ⁿ x) ϵ
≤ⁿ-refl X (p , l , d , c , a) ϵ = (pr₁ ∘ pr₁) (l ϵ)

≤ⁿ-trans
 : (X : ClosenessSpace 𝓤)
 → {_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ }
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤_ _≤ⁿ_
 → (ϵ : ℕ) (x y z : ⟨ X ⟩)
 → (x ≤ⁿ y) ϵ → (y ≤ⁿ z) ϵ → (x ≤ⁿ z) ϵ
≤ⁿ-trans X (p , l , d , c , a) ϵ = (pr₁ ∘ pr₂ ∘ pr₁) (l ϵ)

≤ⁿ-prop
 : (X : ClosenessSpace 𝓤)
 → {_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ }
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤_ _≤ⁿ_
 → (ϵ : ℕ) (x y : ⟨ X ⟩)
 → is-prop ((x ≤ⁿ y) ϵ)
≤ⁿ-prop X (p , l , d , c , a) ϵ = (pr₂ ∘ pr₂ ∘ pr₁) (l ϵ)

≤ⁿ-linear
 : (X : ClosenessSpace 𝓤)
 → {_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ }
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤_ _≤ⁿ_
 → (ϵ : ℕ) (x y : ⟨ X ⟩)
 → (x ≤ⁿ y) ϵ + (y ≤ⁿ x) ϵ
≤ⁿ-linear X (p , l , d , c , a) ϵ = pr₂ (l ϵ)

≤ⁿ-decidable
 : (X : ClosenessSpace 𝓤)
 → {_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ }
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤_ _≤ⁿ_
 → (ϵ : ℕ) (x y : ⟨ X ⟩)
 → is-decidable ((x ≤ⁿ y) ϵ)
≤ⁿ-decidable X (p , l , d , c , a) = d

≤ⁿ-close
 : (X : ClosenessSpace 𝓤)
 → {_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ }
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤_ _≤ⁿ_
 → (ϵ : ℕ) (x y : ⟨ X ⟩)
 → C X ϵ x y → (x ≤ⁿ y) ϵ
≤ⁿ-close X (p , l , d , c , a) = c

≤ⁿ-apart
 : (X : ClosenessSpace 𝓤)
 → {_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ }
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤_ _≤ⁿ_
 → (ϵ : ℕ) (x y : ⟨ X ⟩)
 → ¬ C X ϵ x y → (x ≤ⁿ y) ϵ ⇔ x ≤ y
≤ⁿ-apart X (p , l , d , c , a) ϵ x y f = a ϵ x y f

≤ⁿ-apart→
 : (X : ClosenessSpace 𝓤)
 → {_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ }
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤_ _≤ⁿ_
 → (ϵ : ℕ) (x y : ⟨ X ⟩)
 → ¬ C X ϵ x y → (x ≤ⁿ y) ϵ → x ≤ y
≤ⁿ-apart→ X (p , l , d , c , a) ϵ x y f = pr₁ (a ϵ x y f)

≤ⁿ-apart←
 : (X : ClosenessSpace 𝓤)
 → {_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ }
 → {_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ }
 → is-approx-order X _≤_ _≤ⁿ_
 → (ϵ : ℕ) (x y : ⟨ X ⟩)
 → ¬ C X ϵ x y → x ≤ y → (x ≤ⁿ y) ϵ 
≤ⁿ-apart← X (p , l , d , c , a) ϵ x y f = pr₂ (a ϵ x y f)

apart-total : {X : ClosenessSpace 𝓤}
            → (_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
            → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ )
            → is-approx-order X _≤_ _≤ⁿ_
            → (ϵ : ℕ) (x y : ⟨ X ⟩) 
            → ¬ C X ϵ x y → (x ≤ y) + (y ≤ x)
apart-total {_} {_} {_} {X} _≤_ _≤ⁿ_ a ϵ x y ¬Bϵxy
 = Cases (≤ⁿ-linear X a ϵ x y)
     (inl ∘ ≤ⁿ-apart→ X a ϵ x y ¬Bϵxy)
     (inr ∘ ≤ⁿ-apart→ X a ϵ y x (λ Bϵxy → ¬Bϵxy (C-sym X ϵ y x Bϵxy)))

\end{code}
