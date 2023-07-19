# Ternary signed-digit encodings' suitability for search, optimisation and regression

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import CoNaturals.GenericConvergentSequence
 renaming (ℕ-to-ℕ∞ to _↑) hiding (max)
open import Notation.Order
open import Naturals.Order
open import TypeTopology.DiscreteAndSeparated
open import NotionsOfDecidability.Complemented
open import UF.Subsingletons
open import UF.FunExt
open import UF.Miscelanea
open import UF.Equiv
open import MLTT.Two-Properties

module TWA.Thesis.Chapter6.SignedDigitSearch
  (fe : FunExt) (pe : PropExt) where

open import TWA.Thesis.Chapter2.Finite
open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter2.Vectors
open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe
open import TWA.Thesis.Chapter3.SearchableTypes fe
open import TWA.Thesis.Chapter3.SearchableTypes-Examples fe pe
open import TWA.Thesis.Chapter4.ApproxOrder fe
open import TWA.Thesis.Chapter4.ApproxOrder-Examples fe
open import TWA.Thesis.Chapter4.GlobalOptimisation fe
open import TWA.Thesis.Chapter4.ParametricRegression fe
open import TWA.Thesis.Chapter5.SignedDigit
open import TWA.Thesis.Chapter6.SequenceContinuity fe
open import TWA.Thesis.Chapter6.SignedDigitContinuity fe
open import TWA.Thesis.Chapter6.SignedDigitOrder fe pe

{- 𝟛ᴺ-lexicorder : 𝟛ᴺ → 𝟛ᴺ → 𝓤₀ ̇
𝟛ᴺ-lexicorder
 = discrete-lexicorder 𝟛-is-discrete (finite-strict-order 𝟛-finite)
 

𝟛-is-set : is-set 𝟛
𝟛-is-set = finite-is-set 𝟛-finite

_<₃_ : 𝟛 → 𝟛 → 𝓤₀ ̇
_<₃_ = finite-strict-order 𝟛-finite
-}
{- <₃-is-strict : is-strict-order _<₃_
<₃-is-strict = finite-strict-order-is-strict-order 𝟛-finite

<₃-trichotomous : trichotomous _<₃_
<₃-trichotomous = finite-strict-order-trichotomous 𝟛-finite

𝟛ᴺ-lexicorder-is-preorder : is-preorder 𝟛ᴺ-lexicorder
𝟛ᴺ-lexicorder-is-preorder
 = discrete-lexicorder-is-preorder 𝟛-is-discrete
     𝟛-is-set _<₃_ <₃-is-strict

𝟛ᴺ-approx-lexicorder : 𝟛ᴺ → 𝟛ᴺ → ℕ → 𝓤₀ ̇ 
𝟛ᴺ-approx-lexicorder = discrete-approx-lexicorder 𝟛-is-discrete _<₃_

𝟛ᴺ-approx-lexicorder-is-approx-order
 : is-approx-order' 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-approx-lexicorder
𝟛ᴺ-approx-lexicorder-is-approx-order
 = is-approx-order-ι 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-lexicorder 𝟛ᴺ-approx-lexicorder
    (discrete-approx-lexicorder-is-approx-order-for
      𝟛-is-discrete 𝟛-is-set _<₃_ <₃-is-strict <₃-trichotomous) -}

𝟛ᴺ-totally-bounded : totally-bounded 𝟛ᴺ-ClosenessSpace 𝓤₀
𝟛ᴺ-totally-bounded = ℕ→F-totally-bounded 𝟛-is-discrete 𝟛-is-finite O

𝟛ᴺ×𝟛ᴺ-totally-bounded : totally-bounded 𝟛ᴺ×𝟛ᴺ-ClosenessSpace 𝓤₀
𝟛ᴺ×𝟛ᴺ-totally-bounded
 = ×-totally-bounded
     𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
     𝟛ᴺ-totally-bounded 𝟛ᴺ-totally-bounded



𝟛ᴺ→𝟛ᴺ-global-opt : (f : 𝟛ᴺ → 𝟛ᴺ)
                 → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace f
                 → (ϵ : ℕ)
                 → (has ϵ global-minimal) _≤ⁿ𝟛ᴺ_ f
𝟛ᴺ→𝟛ᴺ-global-opt f ϕ ϵ
 = global-opt 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
     (repeat O)
     _≤ⁿ𝟛ᴺ_
     ≤ⁿ𝟛ᴺ-is-approx-order
     ϵ f ϕ
     𝟛ᴺ-totally-bounded

 {- 𝟛ᴺ-approx-lexicorder
     𝟛ᴺ-approx-lexicorder-is-approx-order ϵ f ϕ
     𝟛ᴺ-totally-bounded  -}

𝟛ᴺ-csearchable-tb 𝟛ᴺ-csearchable
 : {𝓦 : Universe} → csearchable 𝓦 𝟛ᴺ-ClosenessSpace
𝟛ᴺ-csearchable-tb
 = totally-bounded-csearchable
     𝟛ᴺ-ClosenessSpace (repeat O) 𝟛ᴺ-totally-bounded

𝟛ᴺ-csearchable = discrete-finite-seq-csearchable O 𝟛-is-finite 𝟛-is-discrete

𝟛ᴺ×𝟛ᴺ-csearchable-tb 𝟛ᴺ×𝟛ᴺ-csearchable
 : {𝓦 : Universe} → csearchable 𝓦 𝟛ᴺ×𝟛ᴺ-ClosenessSpace
𝟛ᴺ×𝟛ᴺ-csearchable-tb
 = totally-bounded-csearchable
     𝟛ᴺ×𝟛ᴺ-ClosenessSpace (repeat O , repeat O) 𝟛ᴺ×𝟛ᴺ-totally-bounded
𝟛ᴺ×𝟛ᴺ-csearchable
 = ×-csearchable 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
     𝟛ᴺ-csearchable 𝟛ᴺ-csearchable

{- 𝟛ᴺ-approx-lexicorder-l-decidable
 : (ε : ℕ) (y : 𝟛ᴺ)
 → is-complemented (λ x → 𝟛ᴺ-approx-lexicorder x y ε)
𝟛ᴺ-approx-lexicorder-l-decidable ε x y
 = ≤ⁿ-decidable 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-approx-lexicorder-is-approx-order
     ε y x -}

-- Move to approx order

{-  -}

{- 𝟛ᴺ-approx-lexicorder-r-ucontinuous
 : (ε : ℕ) (y : 𝟛ᴺ)
 → p-ucontinuous
     𝟛ᴺ-ClosenessSpace (λ x → 𝟛ᴺ-approx-lexicorder' y x ε)
𝟛ᴺ-approx-lexicorder-r-ucontinuous
 = approx-order-r-ucontinuous
     𝟛ᴺ-ClosenessSpace 𝟛ᴺ-approx-lexicorder
     𝟛ᴺ-approx-lexicorder-is-approx-order -}


{- 𝟛ᴺ-approx-lexicorder-l-f-ucontinuous
 : (ε : ℕ) (y : 𝟛ᴺ)
 → (f : 𝟛ᴺ → 𝟛ᴺ)
 → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace f
 → p-ucontinuous
     𝟛ᴺ-ClosenessSpace (λ x → 𝟛ᴺ-approx-lexicorder' (f x) y ε)
𝟛ᴺ-approx-lexicorder-l-f-ucontinuous ε ζ f ϕ
 = p-ucontinuous-comp 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
     f ϕ
     (λ α → 𝟛ᴺ-approx-lexicorder' α ζ ε)
     (𝟛ᴺ-approx-lexicorder-l-ucontinuous ε ζ)

𝟛ᴺ-approx-lexicorder-r-f-ucontinuous
 : (ε : ℕ) (y : 𝟛ᴺ)
 → (f : 𝟛ᴺ → 𝟛ᴺ)
 → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace f
 → p-ucontinuous
     𝟛ᴺ-ClosenessSpace (λ x → 𝟛ᴺ-approx-lexicorder' y (f x) ε)
𝟛ᴺ-approx-lexicorder-r-f-ucontinuous ε ζ f ϕ
 = p-ucontinuous-comp 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
     f ϕ
     (λ α → 𝟛ᴺ-approx-lexicorder' ζ α ε)
     (𝟛ᴺ-approx-lexicorder-r-ucontinuous ε ζ) -}

𝟚ᴺ : 𝓤₀ ̇
𝟚ᴺ = ℕ → 𝟚

𝟚ᴺ-lexicorder : 𝟚ᴺ → 𝟚ᴺ → 𝓤₀ ̇
𝟚ᴺ-lexicorder
 = discrete-lexicorder 𝟚-is-discrete _<₂_

𝟚ᴺ-lexicorder-is-preorder : is-preorder 𝟚ᴺ-lexicorder
𝟚ᴺ-lexicorder-is-preorder
 = discrete-lexicorder-is-preorder 𝟚-is-discrete
     𝟚-is-set _<₂_ <₂-is-strict

𝟚ᴺ-approx-lexicorder : 𝟚ᴺ → 𝟚ᴺ → ℕ → 𝓤₀ ̇ 
𝟚ᴺ-approx-lexicorder = discrete-approx-lexicorder 𝟚-is-discrete _<₂_

𝟚ᴺ-approx-lexicorder-is-approx-order
 : is-approx-order 𝟚ᴺ-ClosenessSpace 𝟚ᴺ-approx-lexicorder
𝟚ᴺ-approx-lexicorder-is-approx-order
 = discrete-approx-lexicorder-is-approx-order
       𝟚-is-discrete 𝟚-is-set _<₂_ (<₂-is-strict , <₂-trichotomous)

𝟚ᴺ-approx-lexicorder' : 𝟚ᴺ → 𝟚ᴺ → ℕ → Ω 𝓤₀
𝟚ᴺ-approx-lexicorder' α β n
 = 𝟚ᴺ-approx-lexicorder α β n
 , ≤ⁿ-prop 𝟚ᴺ-ClosenessSpace 𝟚ᴺ-approx-lexicorder-is-approx-order n α β

𝟚ᴺ-totally-bounded : totally-bounded 𝟚ᴺ-ClosenessSpace 𝓤₀
𝟚ᴺ-totally-bounded = ℕ→F-totally-bounded 𝟚-is-discrete 𝟚-is-finite ₀

𝟚ᴺ×𝟚ᴺ-totally-bounded : totally-bounded 𝟚ᴺ×𝟚ᴺ-ClosenessSpace 𝓤₀
𝟚ᴺ×𝟚ᴺ-totally-bounded
 = ×-totally-bounded
     𝟚ᴺ-ClosenessSpace 𝟚ᴺ-ClosenessSpace
     𝟚ᴺ-totally-bounded 𝟚ᴺ-totally-bounded

𝟚ᴺ→𝟛ᴺ-global-opt : (f : 𝟚ᴺ → 𝟛ᴺ)
                 → f-ucontinuous 𝟚ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace f
                 → (ϵ : ℕ)
                 → (has ϵ global-minimal) _≤ⁿ𝟛ᴺ_ f
𝟚ᴺ→𝟛ᴺ-global-opt f ϕ ϵ
 = global-opt 𝟚ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
     (repeat ₀)
     _≤ⁿ𝟛ᴺ_
     ≤ⁿ𝟛ᴺ-is-approx-order
     ϵ f ϕ
     𝟚ᴺ-totally-bounded


{-
𝟚ᴺ-global-opt¹ : (f : 𝟚ᴺ → 𝟛ᴺ)
               → f-ucontinuous 𝟚ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace f
               → (ϵ : ℕ)
               → (has ϵ global-minimal) 𝟚ᴺ-approx-lexicorder f
𝟚ᴺ-global-opt¹ f ϕ ϵ
 = global-opt 𝟚ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
     (repeat ₀) 𝟚ᴺ-lexicorder 𝟚ᴺ-approx-lexicorder
     𝟚ᴺ-approx-lexicorder-is-approx-order ϵ f ϕ
     𝟚ᴺ-totally-bounded
-}

𝟚ᴺ-csearchable-tb 𝟚ᴺ-csearchable
 : {𝓦 : Universe} → csearchable 𝓦 𝟚ᴺ-ClosenessSpace
𝟚ᴺ-csearchable-tb
 = totally-bounded-csearchable
     𝟚ᴺ-ClosenessSpace (repeat ₀) 𝟚ᴺ-totally-bounded
𝟚ᴺ-csearchable = discrete-finite-seq-csearchable ₀ 𝟚-is-finite 𝟚-is-discrete

𝟚ᴺ×𝟚ᴺ-csearchable-tb 𝟚ᴺ×𝟚ᴺ-csearchable
 : {𝓦 : Universe} → csearchable 𝓦 𝟚ᴺ×𝟚ᴺ-ClosenessSpace
𝟚ᴺ×𝟚ᴺ-csearchable-tb
 = totally-bounded-csearchable
     𝟚ᴺ×𝟚ᴺ-ClosenessSpace (repeat ₀ , repeat ₀) 𝟚ᴺ×𝟚ᴺ-totally-bounded
𝟚ᴺ×𝟚ᴺ-csearchable
 = ×-csearchable 𝟚ᴺ-ClosenessSpace 𝟚ᴺ-ClosenessSpace
     𝟚ᴺ-csearchable 𝟚ᴺ-csearchable

𝟚ᴺ-approx-lexicorder-l-decidable
 : (ε : ℕ) (y : 𝟚ᴺ)
 → is-complemented (λ x → 𝟚ᴺ-approx-lexicorder x y ε)
𝟚ᴺ-approx-lexicorder-l-decidable ε x y
 = ≤ⁿ-decidable 𝟚ᴺ-ClosenessSpace 𝟚ᴺ-approx-lexicorder-is-approx-order
     ε y x

𝟚ᴺ-approx-lexicorder-l-ucontinuous
 : (ε : ℕ) (y : 𝟚ᴺ)
 → p-ucontinuous
     𝟚ᴺ-ClosenessSpace (λ x → 𝟚ᴺ-approx-lexicorder' x y ε)
𝟚ᴺ-approx-lexicorder-l-ucontinuous ε y = ε , γ
 where
  γ : (x₁ x₂ : 𝟚ᴺ) → C 𝟚ᴺ-ClosenessSpace ε x₁ x₂
    → 𝟚ᴺ-approx-lexicorder' x₁ y ε holds
    → 𝟚ᴺ-approx-lexicorder' x₂ y ε holds
  γ x₁ x₂ Cx₁x₂ (inl x₁∼ᵉy)
   = inl (λ i i<ε → C-to-∼ⁿ 𝟚-is-discrete x₁ x₂ ε Cx₁x₂ i i<ε ⁻¹
                  ∙ x₁∼ᵉy i i<ε)
  γ x₁ x₂ Cx₁x₂ (inr (i , i<ε , x₁∼ⁱy , x₁i<yi))
   = inr (i , i<ε
       , (λ j j<i → C-to-∼ⁿ 𝟚-is-discrete x₁ x₂ ε Cx₁x₂ j
                      (<-trans j i ε j<i i<ε) ⁻¹
                  ∙ x₁∼ⁱy j j<i)
       , transport (_<₂ y i)
           (C-to-∼ⁿ 𝟚-is-discrete x₁ x₂ ε Cx₁x₂ i i<ε) x₁i<yi) 
```
