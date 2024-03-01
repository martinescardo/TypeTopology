[⇐ Index](../html/TWA.Thesis.index.html)

# Ternary signed-digit encodings' suitability for search, optimisation and regression

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.DiscreteAndSeparated
open import UF.Subsingletons
open import UF.FunExt
open import MLTT.Two-Properties
open import UF.SubtypeClassifier

module TWA.Thesis.Chapter6.SignedDigitSearch
  (fe : FunExt) (pe : PropExt) where

open import TWA.Thesis.Chapter2.Finite
open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter3.ClosenessSpaces fe
 hiding (decidable-predicate;decidable-uc-predicate)
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe
open import TWA.Thesis.Chapter3.SearchableTypes fe
open import TWA.Thesis.Chapter3.SearchableTypes-Examples fe pe
open import TWA.Thesis.Chapter4.ApproxOrder fe
open import TWA.Thesis.Chapter4.ApproxOrder-Examples fe
open import TWA.Thesis.Chapter4.GlobalOptimisation fe
open import TWA.Thesis.Chapter5.SignedDigit
open import TWA.Thesis.Chapter6.SequenceContinuity fe
open import TWA.Thesis.Chapter6.SignedDigitOrder fe
```

## Totally bounded

```
𝟛ᴺ-totally-bounded : totally-bounded 𝟛ᴺ-ClosenessSpace 𝓤₀
𝟛ᴺ-totally-bounded = ℕ→F-totally-bounded 𝟛-is-discrete 𝟛-is-finite O

𝟛ᴺ×𝟛ᴺ-totally-bounded : totally-bounded 𝟛ᴺ×𝟛ᴺ-ClosenessSpace 𝓤₀
𝟛ᴺ×𝟛ᴺ-totally-bounded
 = ×-totally-bounded
     𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
     𝟛ᴺ-totally-bounded 𝟛ᴺ-totally-bounded
```

## Global optimisation

```
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
```

## Uniformly continuously searchable

```
𝟛ᴺ-csearchable-tb 𝟛ᴺ-csearchable
 : {𝓦 : Universe} → csearchable 𝓦 𝟛ᴺ-ClosenessSpace
𝟛ᴺ-csearchable-tb
 = totally-bounded-csearchable
     𝟛ᴺ-ClosenessSpace (repeat O) 𝟛ᴺ-totally-bounded
𝟛ᴺ-csearchable
 = discrete-finite-seq-csearchable O 𝟛-is-finite 𝟛-is-discrete

𝟛ᴺ×𝟛ᴺ-csearchable-tb 𝟛ᴺ×𝟛ᴺ-csearchable
 : {𝓦 : Universe} → csearchable 𝓦 𝟛ᴺ×𝟛ᴺ-ClosenessSpace
𝟛ᴺ×𝟛ᴺ-csearchable-tb
 = totally-bounded-csearchable
     𝟛ᴺ×𝟛ᴺ-ClosenessSpace (repeat O , repeat O) 𝟛ᴺ×𝟛ᴺ-totally-bounded
𝟛ᴺ×𝟛ᴺ-csearchable
 = ×-csearchable 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
     𝟛ᴺ-csearchable 𝟛ᴺ-csearchable
```

## Cantor space search and optimisation

```
≤₂-is-preorder : is-preorder _≤₂_
≤₂-is-preorder
 = (λ _ → ≤₂-refl) , ≤₂-trans , λ _ _ → ≤₂-is-prop-valued

≤₂-is-antisym-preorder : is-partial-order _≤₂_
≤₂-is-antisym-preorder = ≤₂-is-preorder , λ _ _ → ≤₂-anti

≤₂-is-antisym-linear-preorder : is-linear-order _≤₂_
≤₂-is-antisym-linear-preorder = ≤₂-is-antisym-preorder , ≤₂-linear
 where
  ≤₂-linear : linear _≤₂_
  ≤₂-linear ₀ _ = inl ⋆
  ≤₂-linear ₁ ₀ = inr ⋆
  ≤₂-linear ₁ ₁ = inl ⋆

𝟚ᴺ : 𝓤₀ ̇
𝟚ᴺ = ℕ → 𝟚

𝟚ᴺ-lexicorder : 𝟚ᴺ → 𝟚ᴺ → 𝓤₀ ̇
𝟚ᴺ-lexicorder
 = discrete-lexicorder 𝟚-is-discrete _≤₂_

𝟚ᴺ-lexicorder-is-preorder : is-preorder 𝟚ᴺ-lexicorder
𝟚ᴺ-lexicorder-is-preorder
 = discrete-lexicorder-is-preorder
     𝟚-is-discrete _≤₂_ ≤₂-is-antisym-preorder

𝟚ᴺ-approx-lexicorder : 𝟚ᴺ → 𝟚ᴺ → ℕ → 𝓤₀ ̇ 
𝟚ᴺ-approx-lexicorder = discrete-approx-lexicorder 𝟚-is-discrete _≤₂_

𝟚ᴺ-approx-lexicorder-is-approx-order
 : is-approx-order 𝟚ᴺ-ClosenessSpace 𝟚ᴺ-approx-lexicorder
𝟚ᴺ-approx-lexicorder-is-approx-order
 = discrete-approx-lexicorder-is-approx-order
       𝟚-is-discrete _≤₂_
       ≤₂-is-antisym-linear-preorder 

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

𝟚ᴺ-csearchable-tb 𝟚ᴺ-csearchable
 : {𝓦 : Universe} → csearchable 𝓦 𝟚ᴺ-ClosenessSpace
𝟚ᴺ-csearchable-tb
 = totally-bounded-csearchable
     𝟚ᴺ-ClosenessSpace (repeat ₀) 𝟚ᴺ-totally-bounded
𝟚ᴺ-csearchable
 = discrete-finite-seq-csearchable ₀ 𝟚-is-finite 𝟚-is-discrete

𝟚ᴺ×𝟚ᴺ-csearchable-tb 𝟚ᴺ×𝟚ᴺ-csearchable
 : {𝓦 : Universe} → csearchable 𝓦 𝟚ᴺ×𝟚ᴺ-ClosenessSpace
𝟚ᴺ×𝟚ᴺ-csearchable-tb
 = totally-bounded-csearchable
     𝟚ᴺ×𝟚ᴺ-ClosenessSpace (repeat ₀ , repeat ₀) 𝟚ᴺ×𝟚ᴺ-totally-bounded
𝟚ᴺ×𝟚ᴺ-csearchable
 = ×-csearchable 𝟚ᴺ-ClosenessSpace 𝟚ᴺ-ClosenessSpace
     𝟚ᴺ-csearchable 𝟚ᴺ-csearchable
```

## Conversion from Cantor sequence to ternary signed-digit encoding

```

𝟚→𝟛 : 𝟚 → 𝟛
𝟚→𝟛 ₀ = −1
𝟚→𝟛 ₁ = +1

_↑ : 𝟚ᴺ → 𝟛ᴺ
_↑ = map 𝟚→𝟛

_⤊ : 𝟚ᴺ × 𝟚ᴺ → 𝟛ᴺ × 𝟛ᴺ
_⤊ (α , β) = α ↑ , β ↑

↑-ucontinuous : f-ucontinuous 𝟚ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace _↑
↑-ucontinuous
 = seq-f-ucontinuous¹-to-closeness
     𝟚-is-discrete 𝟛-is-discrete
     _↑ (map-ucontinuous' 𝟚→𝟛)

⤊-ucontinuous
 : f-ucontinuous 𝟚ᴺ×𝟚ᴺ-ClosenessSpace 𝟛ᴺ×𝟛ᴺ-ClosenessSpace _⤊
⤊-ucontinuous ϵ
 = ϵ
 , (λ x₁ x₂ Cx₁x₂
 → ×-C-combine 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
     (pr₁ (x₁ ⤊)) (pr₁ (x₂ ⤊))
     (pr₂ (x₁ ⤊)) (pr₂ (x₂ ⤊))
     ϵ
     (pr₂ (↑-ucontinuous ϵ) (pr₁ x₁) (pr₁ x₂)
       (×-C-left 𝟚ᴺ-ClosenessSpace 𝟚ᴺ-ClosenessSpace
         (pr₁ x₁) (pr₁ x₂)
         (pr₂ x₁) (pr₂ x₂)
         ϵ Cx₁x₂))
     (pr₂ (↑-ucontinuous ϵ) (pr₂ x₁) (pr₂ x₂)
       (×-C-right 𝟚ᴺ-ClosenessSpace 𝟚ᴺ-ClosenessSpace
         (pr₁ x₁) (pr₁ x₂)
         (pr₂ x₁) (pr₂ x₂)
         ϵ Cx₁x₂)))

↑-pred : decidable-uc-predicate 𝓦 𝟛ᴺ-ClosenessSpace
       → decidable-uc-predicate 𝓦 𝟚ᴺ-ClosenessSpace
↑-pred ((p , d) , ϕ)
 = (p ∘ _↑ , d ∘ _↑)
 , p-ucontinuous-comp 𝟚ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
     _↑ ↑-ucontinuous p ϕ

⤊-pred : decidable-uc-predicate 𝓦 𝟛ᴺ×𝟛ᴺ-ClosenessSpace
                 → decidable-uc-predicate 𝓦 𝟚ᴺ×𝟚ᴺ-ClosenessSpace
⤊-pred ((p , d) , ϕ)
 = (p ∘ _⤊ , d ∘ _⤊)
 , p-ucontinuous-comp 𝟚ᴺ×𝟚ᴺ-ClosenessSpace 𝟛ᴺ×𝟛ᴺ-ClosenessSpace
     _⤊ ⤊-ucontinuous p ϕ
```

[⇐ Index](../html/TWA.Thesis.index.html)
