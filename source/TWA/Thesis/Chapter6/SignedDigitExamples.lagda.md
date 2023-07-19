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
open import MLTT.SpartanList hiding (_∷_;⟨_⟩;[_])

module TWA.Thesis.Chapter6.SignedDigitExamples
  (fe : FunExt) (pe : PropExt) where

open import TWA.Thesis.Chapter2.Finite
open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter2.Vectors
open import TWA.Thesis.Chapter3.ClosenessSpaces fe
 hiding (decidable-predicate;decidable-uc-predicate)
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
open import TWA.Thesis.Chapter6.SignedDigitSearch fe pe
open import TWA.Thesis.Chapter6.SignedDigitOrder fe pe

𝟚→𝟛 : 𝟚 → 𝟛
𝟚→𝟛 ₀ = −1
𝟚→𝟛 ₁ = +1

𝟚ᴺ→𝟛ᴺ : 𝟚ᴺ → 𝟛ᴺ
𝟚ᴺ→𝟛ᴺ = map 𝟚→𝟛

-1𝟚ᴺ -1/2𝟚ᴺ O𝟚ᴺ 1/4𝟚ᴺ 1/3𝟚ᴺ 1/2𝟚ᴺ 1𝟚ᴺ : 𝟚ᴺ
-1𝟚ᴺ   = repeat ₀
-1/2𝟚ᴺ = ₀ ∷ (₀ ∷ repeat ₁)
O𝟚ᴺ    = ₀ ∷ repeat ₁
1/4𝟚ᴺ  = ₀ ∷ (₁ ∷ (₀ ∷ repeat ₁))
1/2𝟚ᴺ  = ₁ ∷ (₁ ∷ repeat ₀)
1𝟚ᴺ    = repeat ₁
1/3𝟚ᴺ 0 = ₁
1/3𝟚ᴺ 1 = ₀
1/3𝟚ᴺ (succ (succ n)) = 1/3𝟚ᴺ n

-1𝟛ᴺ -1/2𝟛ᴺ O𝟛ᴺ 1/4𝟛ᴺ 1/3𝟛ᴺ 1/2𝟛ᴺ 1𝟛ᴺ : 𝟛ᴺ
-1𝟛ᴺ   = 𝟚ᴺ→𝟛ᴺ -1𝟚ᴺ
-1/2𝟛ᴺ = 𝟚ᴺ→𝟛ᴺ -1/2𝟚ᴺ
O𝟛ᴺ    = 𝟚ᴺ→𝟛ᴺ O𝟚ᴺ
1/4𝟛ᴺ  = 𝟚ᴺ→𝟛ᴺ 1/4𝟚ᴺ
1/3𝟛ᴺ  = 𝟚ᴺ→𝟛ᴺ 1/3𝟚ᴺ
1/2𝟛ᴺ  = 𝟚ᴺ→𝟛ᴺ 1/2𝟚ᴺ
1𝟛ᴺ    = 𝟚ᴺ→𝟛ᴺ 1𝟚ᴺ

𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ : 𝟚ᴺ × 𝟚ᴺ → 𝟛ᴺ × 𝟛ᴺ
𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ (α , β) = (𝟚ᴺ→𝟛ᴺ α) , (𝟚ᴺ→𝟛ᴺ β)

𝟚ᴺ→𝟛ᴺ-ucontinuous
 : f-ucontinuous 𝟚ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟚ᴺ→𝟛ᴺ
𝟚ᴺ→𝟛ᴺ-ucontinuous
 = seq-f-ucontinuous¹-to-closeness
     𝟚-is-discrete 𝟛-is-discrete
     𝟚ᴺ→𝟛ᴺ (map-ucontinuous' 𝟚→𝟛)

𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ-ucontinuous
 : f-ucontinuous 𝟚ᴺ×𝟚ᴺ-ClosenessSpace 𝟛ᴺ×𝟛ᴺ-ClosenessSpace 𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ
𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ-ucontinuous ϵ
 = ϵ
 , (λ x₁ x₂ Cx₁x₂
 → ×-C-combine 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
     (pr₁ (𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ x₁)) (pr₁ (𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ x₂))
     (pr₂ (𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ x₁)) (pr₂ (𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ x₂))
     ϵ
     (pr₂ (𝟚ᴺ→𝟛ᴺ-ucontinuous ϵ) (pr₁ x₁) (pr₁ x₂)
       (×-C-left 𝟚ᴺ-ClosenessSpace 𝟚ᴺ-ClosenessSpace
         (pr₁ x₁) (pr₁ x₂)
         (pr₂ x₁) (pr₂ x₂)
         ϵ Cx₁x₂))
     (pr₂ (𝟚ᴺ→𝟛ᴺ-ucontinuous ϵ) (pr₂ x₁) (pr₂ x₂)
       (×-C-right 𝟚ᴺ-ClosenessSpace 𝟚ᴺ-ClosenessSpace
         (pr₁ x₁) (pr₁ x₂)
         (pr₂ x₁) (pr₂ x₂)
         ϵ Cx₁x₂)))

𝟚ᴺ→𝟛ᴺ-pred : decidable-uc-predicate 𝓦 𝟛ᴺ-ClosenessSpace
           → decidable-uc-predicate 𝓦 𝟚ᴺ-ClosenessSpace
𝟚ᴺ→𝟛ᴺ-pred ((p , d) , ϕ)
 = (p ∘ 𝟚ᴺ→𝟛ᴺ , d ∘ 𝟚ᴺ→𝟛ᴺ)
 , p-ucontinuous-comp 𝟚ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
     𝟚ᴺ→𝟛ᴺ 𝟚ᴺ→𝟛ᴺ-ucontinuous p ϕ

𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ-pred : decidable-uc-predicate 𝓦 𝟛ᴺ×𝟛ᴺ-ClosenessSpace
                 → decidable-uc-predicate 𝓦 𝟚ᴺ×𝟚ᴺ-ClosenessSpace
𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ-pred ((p , d) , ϕ)
 = (p ∘ 𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ , d ∘ 𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ)
 , p-ucontinuous-comp 𝟚ᴺ×𝟚ᴺ-ClosenessSpace 𝟛ᴺ×𝟛ᴺ-ClosenessSpace
     𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ 𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ-ucontinuous p ϕ

≤ⁿ𝟛ᴺ-l-ucontinuous
 : (ε : ℕ) (y : 𝟛ᴺ)
 → p-ucontinuous 𝟛ᴺ-ClosenessSpace (λ x → (x ≤ⁿ𝟛ᴺ' y) ε)
≤ⁿ𝟛ᴺ-l-ucontinuous
 = approx-order-ucontinuous-l
     𝟛ᴺ-ClosenessSpace ≤ⁿ𝟛ᴺ-is-approx-order

≤ⁿ𝟛ᴺ-r-ucontinuous
 : (ε : ℕ) (y : 𝟛ᴺ)
 → p-ucontinuous 𝟛ᴺ-ClosenessSpace (λ x → (y ≤ⁿ𝟛ᴺ' x) ε)
≤ⁿ𝟛ᴺ-r-ucontinuous
 = approx-order-ucontinuous-r
     𝟛ᴺ-ClosenessSpace ≤ⁿ𝟛ᴺ-is-approx-order

module Search-Example1 where

 predicate : ℕ → 𝟛ᴺ → Ω 𝓤₀
 predicate ε x
  = (mid (neg x) (repeat O) ≤ⁿ𝟛ᴺ' 1/4𝟛ᴺ) ε

 predicate-decidable : (ε : ℕ)
                    → is-complemented (λ x → predicate ε x holds)
 predicate-decidable ε x
  = ≤ⁿ𝟛ᴺ-is-decidable ε (mid (neg x) (repeat O)) 1/4𝟛ᴺ 

 predicate-ucontinuous : (ε : ℕ)
                      → p-ucontinuous 𝟛ᴺ-ClosenessSpace
                          (λ x → predicate ε x)
 predicate-ucontinuous ε
  = p-ucontinuous-comp 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
      (λ x → mid (neg x) (repeat O))
      (f-ucontinuous-comp
         𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
         neg (λ x → mid x (repeat O))
         neg-ucontinuous (mid-l-ucontinuous (repeat O)))
      (λ x → (x ≤ⁿ𝟛ᴺ' 1/4𝟛ᴺ) ε)
        (≤ⁿ𝟛ᴺ-l-ucontinuous ε 1/4𝟛ᴺ)

 predicate* : ℕ → decidable-uc-predicate 𝓤₀ 𝟛ᴺ-ClosenessSpace
 predicate* ε = ((λ x → predicate ε x)
             , (predicate-decidable ε))
             , predicate-ucontinuous ε

 search-test-tb : ℕ → 𝟛ᴺ
 search-test-tb ε = pr₁ (𝟛ᴺ-csearchable-tb (predicate* ε))

 search-test : ℕ → 𝟛ᴺ
 search-test ε = pr₁ (𝟛ᴺ-csearchable (predicate* ε))

 search-test-tb' : ℕ → 𝟚ᴺ
 search-test-tb' ε = pr₁ (𝟚ᴺ-csearchable-tb (𝟚ᴺ→𝟛ᴺ-pred (predicate* ε)))

 search-test' : ℕ → 𝟚ᴺ
 search-test' ε = pr₁ (𝟚ᴺ-csearchable (𝟚ᴺ→𝟛ᴺ-pred (predicate* ε)))

module Search-Example2 where

 predicate : ℕ → 𝟛ᴺ → Ω 𝓤₀
 predicate ε x
  = CΩ 𝟛ᴺ-ClosenessSpace ε (mul x x) 1/2𝟛ᴺ

 predicate-decidable : (ε : ℕ)
                    → is-complemented (λ x → predicate ε x holds)
 predicate-decidable ε x
  = C-decidable 𝟛ᴺ-ClosenessSpace ε (mul x x) 1/2𝟛ᴺ

 predicate-ucontinuous : (ε : ℕ)
                      → p-ucontinuous 𝟛ᴺ-ClosenessSpace
                          (λ x → predicate ε x)
 predicate-ucontinuous ε = δ , γ
  where
   δ = pr₁ (mul-ucontinuous ε)
   γ : p-ucontinuous-with-mod 𝟛ᴺ-ClosenessSpace (predicate ε) δ
   γ x₁ x₂ Cx₁x₂
    = C-trans 𝟛ᴺ-ClosenessSpace ε (mul x₂ x₂) (mul x₁ x₁) 1/2𝟛ᴺ
        (pr₂ (mul-ucontinuous ε) (x₂ , x₂) (x₁ , x₁)
          (×-C-combine 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
            x₂ x₁ x₂ x₁ δ
            (C-sym 𝟛ᴺ-ClosenessSpace δ x₁ x₂ Cx₁x₂)
            (C-sym 𝟛ᴺ-ClosenessSpace δ x₁ x₂ Cx₁x₂)))

 predicate* : ℕ → decidable-uc-predicate 𝓤₀ 𝟛ᴺ-ClosenessSpace
 predicate* ε = ((λ x → predicate ε x)
             , (predicate-decidable ε))
             , predicate-ucontinuous ε

 search-test-tb : ℕ → 𝟛ᴺ
 search-test-tb ε = pr₁ (𝟛ᴺ-csearchable-tb (predicate* ε))

 search-test : ℕ → 𝟛ᴺ
 search-test ε = pr₁ (𝟛ᴺ-csearchable (predicate* ε))

 search-test-tb' : ℕ → 𝟚ᴺ
 search-test-tb' ε = pr₁ (𝟚ᴺ-csearchable-tb (𝟚ᴺ→𝟛ᴺ-pred (predicate* ε)))

 search-test' : ℕ → 𝟚ᴺ
 search-test' ε = pr₁ (𝟚ᴺ-csearchable (𝟚ᴺ→𝟛ᴺ-pred (predicate* ε)))

module Search-Example3 where

 predicate : ℕ → 𝟛ᴺ × 𝟛ᴺ → Ω 𝓤₀
 predicate ε (x , y)
  = CΩ 𝟛ᴺ-ClosenessSpace ε (mid x y) (repeat O)

 predicate-decidable : (ε : ℕ)
                    → is-complemented (λ x → predicate ε x holds)
 predicate-decidable ε (x , y)
  = C-decidable 𝟛ᴺ-ClosenessSpace ε (mid x y) (repeat O)

 predicate-ucontinuous : (ε : ℕ)
                      → p-ucontinuous 𝟛ᴺ×𝟛ᴺ-ClosenessSpace
                          (predicate ε)
 predicate-ucontinuous ε = δ , γ
  where
   δ = pr₁ (mid-ucontinuous ε)
   γ : p-ucontinuous-with-mod 𝟛ᴺ×𝟛ᴺ-ClosenessSpace (predicate ε) δ
   γ (x₁ , y₁) (x₂ , y₂) Cxy₁xy₂
    = C-trans 𝟛ᴺ-ClosenessSpace ε (mid x₂ y₂) (mid x₁ y₁) (repeat O)
        (pr₂ (mid-ucontinuous ε) (x₂ , y₂) (x₁ , y₁)
        (C-sym 𝟛ᴺ×𝟛ᴺ-ClosenessSpace δ (x₁ , y₁) (x₂ , y₂) Cxy₁xy₂))

 predicate* : ℕ → decidable-uc-predicate 𝓤₀ 𝟛ᴺ×𝟛ᴺ-ClosenessSpace
 predicate* ε = (predicate ε
             , predicate-decidable ε)
             , predicate-ucontinuous ε

 search-test-tb : ℕ → 𝟛ᴺ × 𝟛ᴺ
 search-test-tb ε = pr₁ (𝟛ᴺ×𝟛ᴺ-csearchable-tb (predicate* ε))

 search-test-tb' : ℕ → 𝟚ᴺ × 𝟚ᴺ
 search-test-tb' ε = pr₁ (𝟚ᴺ×𝟚ᴺ-csearchable-tb (𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ-pred (predicate* ε)))

 search-test : ℕ → 𝟛ᴺ × 𝟛ᴺ
 search-test ε = pr₁ (𝟛ᴺ×𝟛ᴺ-csearchable (predicate* ε))

 search-test' : ℕ → 𝟚ᴺ × 𝟚ᴺ
 search-test' ε = pr₁ (𝟚ᴺ×𝟚ᴺ-csearchable (𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ-pred (predicate* ε)))

module Optimisation-Example1 where

 opt-test : ℕ → 𝟛ᴺ
 opt-test ε = pr₁ (𝟛ᴺ→𝟛ᴺ-global-opt neg neg-ucontinuous ε)

 opt-test' : ℕ → 𝟚ᴺ
 opt-test' ε
  = pr₁ (𝟚ᴺ→𝟛ᴺ-global-opt (neg ∘ 𝟚ᴺ→𝟛ᴺ)
      (f-ucontinuous-comp
         𝟚ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
         𝟚ᴺ→𝟛ᴺ neg
         𝟚ᴺ→𝟛ᴺ-ucontinuous neg-ucontinuous) ε)

module Optimisation-Example2 where

 opt-test : ℕ → 𝟛ᴺ
 opt-test ε = pr₁ (𝟛ᴺ→𝟛ᴺ-global-opt (λ x → mul x x)
                (seq-f-ucontinuous¹-to-closeness
                  𝟛-is-discrete 𝟛-is-discrete
                  (λ x → mul x x)
                  (seq-f-ucontinuous²-both mul mul-ucontinuous'))
                ε)

 opt-test' : ℕ → 𝟚ᴺ
 opt-test' ε
  = pr₁ (𝟚ᴺ→𝟛ᴺ-global-opt ((λ x → mul x x) ∘ 𝟚ᴺ→𝟛ᴺ)
      (f-ucontinuous-comp
         𝟚ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
         𝟚ᴺ→𝟛ᴺ (λ x → mul x x)
         𝟚ᴺ→𝟛ᴺ-ucontinuous
         (seq-f-ucontinuous¹-to-closeness
           𝟛-is-discrete 𝟛-is-discrete
           (λ x → mul x x)
           (seq-f-ucontinuous²-both mul mul-ucontinuous'))) ε)
         
flip-digit : 𝟛ᴺ → ℕ → 𝟛ᴺ
flip-digit α n i with ℕ-is-discrete n i
... | inl _ = flip (α i)
... | inr _ = α i

_/2 _/4 : 𝟛ᴺ → 𝟛ᴺ
x /2 = mid x (repeat O)
x /4 = (x /2) /2 /2

{- module SearchExample
 (X : ClosenessSpace 𝓤)
 (T : totally-bounded X 𝓥)
 (S : csearchable 𝓤₀ X)
 (f : ⟨ X ⟩ → 𝟛ᴺ)
 (ϕf : f-ucontinuous X 𝟛ᴺ-ClosenessSpace f)
 (p : 𝟛ᴺ → Ω 𝓦)
 (d : is-complemented (λ x → p x holds))
 (ϕp : p-ucontinuous 𝟛ᴺ-ClosenessSpace p)
 (from : 
 where -}

module RegressionExample
 (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
 (g : ⟨ Y ⟩ → ⟨ X ⟩)
 (ϕᵍ : f-ucontinuous Y X g)
 (tb : totally-bounded Y 𝓥') 
 (S : csearchable 𝓤₀ Y)
 (M : ⟨ X ⟩ → (𝟛ᴺ → 𝟛ᴺ))
 (𝓞 : 𝟛ᴺ → 𝟛ᴺ)
 {n : ℕ} (observations : Vec 𝟛ᴺ n)
 (ϕᴹ : (y : 𝟛ᴺ) → f-ucontinuous X 𝟛ᴺ-ClosenessSpace λ x → M x y)
 where
          
 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace : (𝟛ᴺ → 𝟛ᴺ) → PseudoClosenessSpace 𝓤₀
 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace f
  = Least-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace f
      observations

 y₀ : ⟨ Y ⟩
 y₀ = csearchable-pointed 𝓤₀ Y S 

 ϕᴸ : (f : 𝟛ᴺ → 𝟛ᴺ)
    → f-ucontinuous' (ι Y)
        (𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace f)
        (λ x → M (g x))
 ϕᴸ = close-to-close Y 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
        (M ∘ g) observations
        (λ y → f-ucontinuous-comp Y X 𝟛ᴺ-ClosenessSpace
               g (λ x → M x y) ϕᵍ (ϕᴹ y))
               
 opt reg : (𝟛ᴺ → 𝟛ᴺ) → ℕ → ⟨ Y ⟩
 opt f ϵ = (pr₁ (optimisation-convergence Y
                    (𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace 𝓞) y₀ tb (M ∘ g) f
                    (ϕᴸ f) ϵ))
 reg f ϵ = (p-regressor Y (𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace 𝓞) S ϵ
               (λ y → M (g y))
               (ϕᴸ f) f)

 reg𝓞 opt𝓞 : ℕ → ⟨ Y ⟩
 reg𝓞  = reg 𝓞
 opt𝓞  = opt 𝓞
 
module RegressionExampleDistortionProne
 (X : ClosenessSpace 𝓤)
 (tb : totally-bounded X 𝓥') 
 (S : csearchable 𝓤₀ X)
 (M : ⟨ X ⟩ → (𝟛ᴺ → 𝟛ᴺ))
 (𝓞 : 𝟛ᴺ → 𝟛ᴺ)
 (Ψ : (𝟛ᴺ → 𝟛ᴺ) → (𝟛ᴺ → 𝟛ᴺ))
 {n : ℕ} (observations : Vec 𝟛ᴺ n)
 (ϕᴹ : (y : 𝟛ᴺ) → f-ucontinuous X 𝟛ᴺ-ClosenessSpace λ x → M x y)
 where

 open RegressionExample X X id (id-ucontinuous X) tb S M (Ψ 𝓞)
        observations ϕᴹ
          
 regΨ𝓞 optΨ𝓞 : ℕ → ⟨ X ⟩
 regΨ𝓞 = reg𝓞
 optΨ𝓞 = opt𝓞

module Regression-Example1a where

 M : 𝟛ᴺ → (𝟛ᴺ → 𝟛ᴺ)
 M x y = mid (neg x) y

 𝓞 : 𝟛ᴺ → 𝟛ᴺ
 𝓞 = mid 1/3𝟛ᴺ

 observations : Vec 𝟛ᴺ 3
 observations = -1𝟛ᴺ :: (O𝟛ᴺ :: [ 1𝟛ᴺ ])

 ϕᴹ : (y : 𝟛ᴺ) → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
                   (λ x → mid (neg x) y)
 ϕᴹ y = f-ucontinuous-comp 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
              𝟛ᴺ-ClosenessSpace neg (λ x → mid x y)
              neg-ucontinuous
              (seq-f-ucontinuous¹-to-closeness
                𝟛-is-discrete 𝟛-is-discrete
                (λ x → mid x y)
                (seq-f-ucontinuous²-left mid mid-ucontinuous' y))
 
 open RegressionExample
   𝟛ᴺ-ClosenessSpace 𝟚ᴺ-ClosenessSpace
   𝟚ᴺ→𝟛ᴺ 𝟚ᴺ→𝟛ᴺ-ucontinuous
   𝟚ᴺ-totally-bounded 𝟚ᴺ-csearchable-tb
   M 𝓞
   observations ϕᴹ
   public

 Ψ : (𝟛ᴺ → 𝟛ᴺ) → (𝟛ᴺ → 𝟛ᴺ)
 Ψ f x = mid x (x /4)

 open RegressionExampleDistortionProne
   𝟛ᴺ-ClosenessSpace
   𝟛ᴺ-totally-bounded 𝟛ᴺ-csearchable-tb
   M 𝓞 Ψ
   observations ϕᴹ
   public 

module Regression-Example1b where

 M : 𝟛ᴺ × 𝟛ᴺ → (𝟛ᴺ → 𝟛ᴺ)
 M (p₁ , p₂) x = mid p₁ (mid p₂ x)

 ϕᴹ : (x : 𝟛ᴺ) → f-ucontinuous 𝟛ᴺ×𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
                   (λ (p₁ , p₂) → mid p₁ (mid p₂ x))
 ϕᴹ x = seq-f-ucontinuous²-to-closeness
          𝟛-is-discrete 𝟛-is-discrete 𝟛-is-discrete
          (λ p₁ p₂ → mid p₁ (mid p₂ x))
          (seq-f-ucontinuous²-comp mid mid
            mid-ucontinuous' mid-ucontinuous' x)

 open Regression-Example1a using (𝓞;observations;Ψ)
 
 open RegressionExample
   𝟛ᴺ×𝟛ᴺ-ClosenessSpace 𝟚ᴺ×𝟚ᴺ-ClosenessSpace
   𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ 𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ-ucontinuous
   𝟚ᴺ×𝟚ᴺ-totally-bounded 𝟚ᴺ×𝟚ᴺ-csearchable-tb
   M 𝓞 observations ϕᴹ
   public

 open RegressionExampleDistortionProne
   𝟛ᴺ×𝟛ᴺ-ClosenessSpace
   𝟛ᴺ×𝟛ᴺ-totally-bounded 𝟛ᴺ×𝟛ᴺ-csearchable-tb
   M 𝓞 Ψ
   observations ϕᴹ
   public 

module Regression-Example2 where

 M : 𝟛ᴺ × 𝟛ᴺ → (𝟛ᴺ → 𝟛ᴺ)
 M (p₁ , p₂) x = mid p₁ (mul p₂ x)

 𝓞 : 𝟛ᴺ → 𝟛ᴺ
 𝓞 = M (1/3𝟛ᴺ , 1/2𝟛ᴺ)

 observations : Vec 𝟛ᴺ 2
 observations = -1/2𝟛ᴺ :: [ 1/2𝟛ᴺ ]

 ϕᴹ : (y : 𝟛ᴺ)
    → f-ucontinuous
        (×-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace)
        𝟛ᴺ-ClosenessSpace (λ x → M x y)
 ϕᴹ y = seq-f-ucontinuous²-to-closeness
           𝟛-is-discrete 𝟛-is-discrete 𝟛-is-discrete
           (λ α β → M (α , β) y)
           (seq-f-ucontinuous²-comp mid mul
             mid-ucontinuous' mul-ucontinuous' y)

 open RegressionExample
   𝟛ᴺ×𝟛ᴺ-ClosenessSpace 𝟚ᴺ×𝟚ᴺ-ClosenessSpace
   𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ 𝟚ᴺ×𝟚ᴺ→𝟛ᴺ×𝟛ᴺ-ucontinuous
   𝟚ᴺ×𝟚ᴺ-totally-bounded 𝟚ᴺ×𝟚ᴺ-csearchable-tb
   M 𝓞 observations ϕᴹ
   public

module RegressionExample1a-Optimisation where

 open Regression-Example1a

 regressed-parameter : ℕ → 𝟛ᴺ
 regressed-parameter = 𝟚ᴺ→𝟛ᴺ ∘ (opt 𝓞)

 regressed-function : ℕ → (𝟛ᴺ → 𝟛ᴺ)
 regressed-function = M ∘ regressed-parameter

module RegressionExample1a-SearchDistortionFree where

 open Regression-Example1a

 regressed-parameter : ℕ → 𝟛ᴺ
 regressed-parameter = 𝟚ᴺ→𝟛ᴺ ∘ (reg𝓞)

 regressed-function : ℕ → (𝟛ᴺ → 𝟛ᴺ)
 regressed-function = M ∘ regressed-parameter

module RegressionExample1a-SearchDistortionProne where

 open Regression-Example1a

 regressed-parameter : ℕ → 𝟛ᴺ
 regressed-parameter = regΨ𝓞

 regressed-function : ℕ → (𝟛ᴺ → 𝟛ᴺ)
 regressed-function = M ∘ regressed-parameter

module RegressionExample1a-OptimisationDistortionProne where

 open Regression-Example1a

 regressed-parameter : ℕ → 𝟛ᴺ
 regressed-parameter = 𝟚ᴺ→𝟛ᴺ ∘ opt (Ψ 𝓞)

 regressed-function : ℕ → (𝟛ᴺ → 𝟛ᴺ)
 regressed-function = M ∘ regressed-parameter

module RegressionExample1b-DistortionProne where

 open Regression-Example1b

 regressed-parameter : ℕ → 𝟛ᴺ × 𝟛ᴺ
 regressed-parameter = regΨ𝓞

 regressed-function : ℕ → (𝟛ᴺ → 𝟛ᴺ)
 regressed-function = M ∘ regressed-parameter

module RegressionExample2-SearchDistortionFree where

 open Regression-Example2

 regressed-parameter : ℕ → 𝟛ᴺ × 𝟛ᴺ
 regressed-parameter ϵ = (𝟚ᴺ→𝟛ᴺ α) , (𝟚ᴺ→𝟛ᴺ β)
  where
   αβ = reg𝓞 ϵ
   α = pr₁ αβ
   β = pr₂ αβ

 regressed-function : ℕ → (𝟛ᴺ → 𝟛ᴺ)
 regressed-function = M ∘ regressed-parameter
```


