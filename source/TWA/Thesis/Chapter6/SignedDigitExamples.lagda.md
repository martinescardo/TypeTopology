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

module TWA.Thesis.Chapter6.SignedDigitExamples
  (fe : FunExt) (pe : PropExt) where

open import TWA.Thesis.Chapter2.FiniteDiscrete
open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter2.Vectors
open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe
open import TWA.Thesis.Chapter3.SearchableTypes fe
open import TWA.Thesis.Chapter3.SearchableTypes-Examples fe pe
open import TWA.Thesis.Chapter4.ApproxOrder fe
open import TWA.Thesis.Chapter4.ApproxOrder-Examples fe
open import TWA.Thesis.Chapter4.GlobalOptimisation fe
open import TWA.Thesis.Chapter4.ConvergenceTheorems fe
open import TWA.Thesis.Chapter5.SignedDigit
open import TWA.Thesis.Chapter6.SequenceContinuity fe
open import TWA.Thesis.Chapter6.SignedDigitContinuity fe
open import TWA.Thesis.Chapter6.SignedDigitSearch fe pe
open import TWA.Thesis.Chapter6.ZeroNormalisation fe pe

𝟚→𝟛 : 𝟚 → 𝟛
𝟚→𝟛 ₀ = −1
𝟚→𝟛 ₁ = +1

𝟚ᴺ→𝟛ᴺ : 𝟚ᴺ → 𝟛ᴺ
𝟚ᴺ→𝟛ᴺ = map 𝟚→𝟛

-1𝟚ᴺ -1/2𝟚ᴺ O𝟚ᴺ 1/4𝟚ᴺ 1/3𝟚ᴺ 1/2𝟚ᴺ 1𝟚ᴺ : 𝟚ᴺ
-1𝟚ᴺ   = repeat ₀
-1/2𝟚ᴺ = ₀ ∶∶ (₀ ∶∶ repeat ₁)
O𝟚ᴺ    = ₀ ∶∶ repeat ₁
1/4𝟚ᴺ  = ₀ ∶∶ (₁ ∶∶ (₀ ∶∶ repeat ₁))
1/2𝟚ᴺ  = ₁ ∶∶ (₁ ∶∶ repeat ₀)
1𝟚ᴺ    = repeat ₁
1/3𝟚ᴺ 0 = ₀
1/3𝟚ᴺ 1 = ₁
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
 = approx-order-l-ucontinuous
     𝟛ᴺ-ClosenessSpace ≤ⁿ𝟛ᴺ-is-approx-order

≤ⁿ𝟛ᴺ-r-ucontinuous
 : (ε : ℕ) (y : 𝟛ᴺ)
 → p-ucontinuous 𝟛ᴺ-ClosenessSpace (λ x → (y ≤ⁿ𝟛ᴺ' x) ε)
≤ⁿ𝟛ᴺ-r-ucontinuous
 = approx-order-r-ucontinuous
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

ℕ∞-vec-min : (n : ℕ) → Vec ℕ∞ n → ℕ∞
ℕ∞-vec-min 0 [] = ∞
ℕ∞-vec-min (succ n) (x ∷ v) = min x (ℕ∞-vec-min n v)

Vec-≃ : {X : 𝓤 ̇ } → (n : ℕ) → Vec X (succ n) ≃ X × Vec X n
Vec-≃ {𝓤} {X} n = qinveq g (h , η , μ)
 where
  g : Vec X (succ n) → X × Vec X n
  g (x ∷ v) = x , v
  h : X × Vec X n → Vec X (succ n)
  h (x , v) = x ∷ v
  η : (λ x → h (g x)) ∼ (λ x → x)
  η (x ∷ v) = refl
  μ : (λ x → g (h x)) ∼ (λ x → x)
  μ (x , v) = refl

open import TWA.Closeness fe hiding (is-ultra;is-closeness)

Vec-ClosenessSpace : (X : ClosenessSpace 𝓤)
                   → (n : ℕ)
                   → ClosenessSpace 𝓤

Vec-clospace : (X : ClosenessSpace 𝓤)
             → (n : ℕ)
             → is-closeness-space (Vec ⟨ X ⟩ n)

Vec-ClosenessSpace X n = (Vec ⟨ X ⟩ n) , Vec-clospace X n

Vec-clospace X 0
 = (λ _ _ → ∞) , e , i , s , u
 where
  e : indistinguishable-are-equal (λ _ _ → ∞)
  e [] [] _ = refl
  i : self-indistinguishable (λ _ _ → ∞)
  i [] = refl
  s : is-symmetric (λ _ _ → ∞)
  s [] [] = refl
  u : is-ultra (λ _ _ → ∞)
  u [] [] [] _ _ = refl
Vec-clospace X (succ n)
 = pr₂ (≃-ClosenessSpace 
     (×-ClosenessSpace X (Vec-ClosenessSpace X n))
     (Vec-≃ n))

FunPoints-clofun : (X : 𝓤 ̇ ) (Y : ClosenessSpace 𝓥)
                 → {n : ℕ}
                 → Vec X n
                 → ((X → ⟨ Y ⟩) → (X → ⟨ Y ⟩) → ℕ∞)
FunPoints-clofun X Y {n} v f g
 = pr₁ (Vec-clospace Y n) (vec-map f v) (vec-map g v)

FunPoints-clofun-is-psclofun
 : (X : 𝓤 ̇ ) (Y : ClosenessSpace 𝓥)
 → {n : ℕ}
 → (v : Vec X n)
 → is-pseudocloseness (FunPoints-clofun X Y v)
FunPoints-clofun-is-psclofun X Y {n} v
 = (λ f → pr₁ (pr₂ γ) (vec-map f v))
 , (λ f g → pr₁ (pr₂ (pr₂ γ)) (vec-map f v) (vec-map g v))
 , (λ f g h → pr₂ (pr₂ (pr₂ γ)) (vec-map f v) (vec-map g v) (vec-map h v))
 where
  γ : is-closeness (pr₁ (Vec-clospace Y n))
  γ = pr₂ (Vec-clospace Y n)

FunPoints-PseudoClosenessSpace : (X : 𝓤 ̇ ) (Y : ClosenessSpace 𝓥)
                               → (f : X → ⟨ Y ⟩)
                               → {n : ℕ}
                               → Vec X n
                               → PseudoClosenessSpace (𝓤 ⊔ 𝓥)
FunPoints-PseudoClosenessSpace X Y f v
 = (X → ⟨ Y ⟩)
 , FunPoints-clofun X Y v
 , FunPoints-clofun-is-psclofun X Y v

open import MLTT.Two-Properties

close-to-close : (X : ClosenessSpace 𝓤)
               → (Y : ClosenessSpace 𝓥)
               → (Z : ClosenessSpace 𝓦)
               → (f : ⟨ X ⟩ → ⟨ Y ⟩ → ⟨ Z ⟩)
               → {n : ℕ} (v : Vec ⟨ Y ⟩ n)
               → ((y : ⟨ Y ⟩) → f-ucontinuous X Z (λ x → f x y))
               → ((g : ⟨ Y ⟩ → ⟨ Z ⟩) → f-ucontinuous' (ι X)
                   (FunPoints-PseudoClosenessSpace ⟨ Y ⟩ Z g v)
                   f)
close-to-close X Y Z f [] _ k ε = 0 , λ _ _ _ _ _ → refl
close-to-close X Y Z f v@(y ∷ ys) ϕʸ g ε = δ , γ
 where
  IH = close-to-close X Y Z f ys ϕʸ g ε
  δ δ₁ δ₂ : ℕ
  δ₁ = pr₁ (ϕʸ y ε)
  δ₂ = pr₁ IH
  δ = max δ₁ δ₂
  γ : (x₁ x₂ : ⟨ X ⟩) → C X δ x₁ x₂
    → C' (FunPoints-PseudoClosenessSpace ⟨ Y ⟩ Z g v) ε (f x₁) (f x₂)
  γ x₁ x₂ Cx₁x₂ n z
   = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
       (pr₂ (ϕʸ y ε) x₁ x₂
         (C-prev X δ δ₁ (max-≤-upper-bound δ₁ δ₂) x₁ x₂ Cx₁x₂) n z)
       (pr₂ IH x₁ x₂
         (C-prev X δ δ₂ (max-≤-upper-bound' δ₂ δ₁) x₁ x₂ Cx₁x₂) n z)
         
flip-digit : 𝟛ᴺ → ℕ → 𝟛ᴺ
flip-digit α n i with ℕ-is-discrete n i
... | inl _ = flip (α i)
... | inr _ = α i

_/2 _/4 : 𝟛ᴺ → 𝟛ᴺ
x /2 = O :: x
x /4 = (x /2) /2

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
 (Ψ : (𝟛ᴺ → 𝟛ᴺ) → (𝟛ᴺ → 𝟛ᴺ))
 {n : ℕ} (observations : Vec 𝟛ᴺ n)
 (ϕᴹ : (y : 𝟛ᴺ) → f-ucontinuous X 𝟛ᴺ-ClosenessSpace λ x → M x y)
 where
          
 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace : (𝟛ᴺ → 𝟛ᴺ) → PseudoClosenessSpace 𝓤₀
 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace f
  = FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace f
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

 reg𝓞 regΨ𝓞 opt𝓞 optΨ𝓞 : ℕ → ⟨ Y ⟩
 reg𝓞  = reg 𝓞
 regΨ𝓞 = reg (Ψ 𝓞)
 opt𝓞  = opt 𝓞
 optΨ𝓞 = opt (Ψ 𝓞)


module Regression-Example1a where

 M : 𝟛ᴺ → (𝟛ᴺ → 𝟛ᴺ)
 M x y = mid (neg x) y

 𝓞 : 𝟛ᴺ → 𝟛ᴺ
 𝓞 = mid 1/3𝟛ᴺ

 observations : Vec 𝟛ᴺ 3
 observations = -1𝟛ᴺ ∷ (O𝟛ᴺ ∷ [ 1𝟛ᴺ ])

 Ψ : (𝟛ᴺ → 𝟛ᴺ) → (𝟛ᴺ → 𝟛ᴺ)
 Ψ f x = f (mid x (x /4))

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
   𝟚ᴺ-totally-bounded 𝟚ᴺ-csearchable
   M 𝓞 Ψ
   observations ϕᴹ
   public 
```
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
   𝟚ᴺ×𝟚ᴺ-totally-bounded 𝟚ᴺ×𝟚ᴺ-csearchable
   M 𝓞 Ψ observations ϕᴹ
   public

module Regression-Example2 where

 M : 𝟛ᴺ × 𝟛ᴺ → (𝟛ᴺ → 𝟛ᴺ)
 M (p₁ , p₂) x = mid p₁ (mul p₂ x)

 𝓞 : 𝟛ᴺ → 𝟛ᴺ
 𝓞 = M (1/3𝟛ᴺ , -1𝟛ᴺ)

 observations : Vec 𝟛ᴺ 2
 observations = -1/2𝟛ᴺ ∷ [ 1/2𝟛ᴺ ]

 Ψ : (𝟛ᴺ → 𝟛ᴺ) → (𝟛ᴺ → 𝟛ᴺ)
 Ψ f x = mid O𝟛ᴺ (f x)

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
   𝟚ᴺ×𝟚ᴺ-totally-bounded 𝟚ᴺ×𝟚ᴺ-csearchable
   M 𝓞 Ψ observations ϕᴹ
   public
  
{-
module Regression-Example3a where

 M : 𝟛ᴺ → (𝟛ᴺ → 𝟛ᴺ)
 M y x = neg (mid y x)

 𝓞 : 𝟛ᴺ → 𝟛ᴺ
 𝓞 x = neg (mul x x)

 observations : Vec 𝟛ᴺ 4
 observations = -1𝟛ᴺ ∷ (-3/4𝟛ᴺ ∷ (-1/2𝟛ᴺ ∷ [ -1/4𝟛ᴺ ]))

 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace : PseudoClosenessSpace 𝓤₀
 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace
  = FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace 𝓞 observations
 
 ϕᴹ' : f-ucontinuous
         (×-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace)
         𝟛ᴺ-ClosenessSpace (uncurry M)
 ϕᴹ' = seq-f-ucontinuous²-to-closeness
         𝟛-is-discrete 𝟛-is-discrete 𝟛-is-discrete
         M (seq-f-ucontinuous¹²-comp neg mid
             neg-ucontinuous' mid-ucontinuous')
           
 ϕᴹ : f-ucontinuous' (ι 𝟛ᴺ-ClosenessSpace) 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace M
 ϕᴹ = {!!}
 {- close-to-close'
        𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
        M 𝓞 observations ϕᴹ' -}

 reg : ℕ → (𝟛ᴺ → 𝟛ᴺ) → 𝟛ᴺ
 reg ε = p-regressor 𝟛ᴺ-ClosenessSpace 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace
          𝟛ᴺ-csearchable ε M ϕᴹ

module Regression-Example3b where

 M : 𝟛ᴺ → (𝟛ᴺ → 𝟛ᴺ)
 M y x = neg (mid y x)

 𝓞 : 𝟛ᴺ → 𝟛ᴺ
 𝓞 x = neg (mul x x)

 observations : Vec 𝟛ᴺ 2
 observations = O𝟛ᴺ ∷ [ 1/2𝟛ᴺ ]

 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace : PseudoClosenessSpace 𝓤₀
 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace
  = FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace 𝓞 observations
 
 ϕᴹ' : f-ucontinuous
         (×-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace)
         𝟛ᴺ-ClosenessSpace (uncurry M)
 ϕᴹ' = seq-f-ucontinuous²-to-closeness
         𝟛-is-discrete 𝟛-is-discrete 𝟛-is-discrete
         M (seq-f-ucontinuous¹²-comp neg mid
             neg-ucontinuous' mid-ucontinuous')
           
 ϕᴹ : f-ucontinuous' (ι 𝟛ᴺ-ClosenessSpace) 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace M
 ϕᴹ = close-to-close
        𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
        M observations
        {!!} {- (λ y → f-ucontinuous-comp
                 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
                 (λ x → mid x y) neg
                 (seq-f-ucontinuous¹-to-closeness
                   𝟛-is-discrete 𝟛-is-discrete
                   (λ x → mid x y)
                   (seq-f-ucontinuous²-left mid mid-ucontinuous' y))
                 neg-ucontinuous)
          𝓞

 reg : ℕ → (𝟛ᴺ → 𝟛ᴺ) → 𝟛ᴺ
 reg ε = p-regressor 𝟛ᴺ-ClosenessSpace 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace
          𝟛ᴺ-csearchable ε M ϕᴹ
-}

module RegressionExample1a-Optimisation where

 open Regression-Example1a

 regressed-parameter : ℕ → 𝟛ᴺ
 regressed-parameter = opt 𝓞

 regressed-function : ℕ → (𝟛ᴺ → 𝟛ᴺ)
 regressed-function = M ∘ regressed-parameter

module RegressionExample1a-SearchDistortionFree where

 open Regression-Example1a

 regressed-parameter : ℕ → 𝟛ᴺ
 regressed-parameter = reg𝓞

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
 regressed-parameter = opt (Ψ 𝓞)

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
 regressed-parameter = reg𝓞

 regressed-function : ℕ → (𝟛ᴺ → 𝟛ᴺ)
 regressed-function = M ∘ regressed-parameter

module RegressionExample3a-SearchDistortionFree where

 open Regression-Example3a

 regressed-parameter : ℕ → 𝟛ᴺ
 regressed-parameter ε = reg ε 𝓞

 regressed-function : ℕ → (𝟛ᴺ → 𝟛ᴺ)
 regressed-function = M ∘ regressed-parameter

module RegressionExample3b-SearchDistortionFree where

 open Regression-Example3b

 regressed-parameter : ℕ → 𝟛ᴺ
 regressed-parameter ε = reg ε 𝓞

 regressed-function : ℕ → (𝟛ᴺ → 𝟛ᴺ)
 regressed-function = M ∘ regressed-parameter
-}


{-
perfect-regression-test : {n : ℕ} → ℕ → Vec 𝟛ᴺ n → (𝟛ᴺ → 𝟛ᴺ)
perfect-regression-test {n} ε v
 = ω
 where
  M : 𝟛ᴺ → (𝟛ᴺ → 𝟛ᴺ)
  M y = λ x → mid y (mul x x)
  k : 𝟛ᴺ
  k = 1/3𝟛ᴺ
  Ω' = M k -- Ω(x) ≔ (1/3 + x²) / 2
  𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace
   = FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace Ω' v
  ϕᴹ' : (y : 𝟛ᴺ) → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
                     (λ x → mid y (mul x x))
  ϕᴹ' y = f-ucontinuous-comp
            𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
            (λ x → mul x x) (mid y)
            mul-b-ucontinuous (mid-r-ucontinuous y)
  ϕᴹ'' : (x : 𝟛ᴺ) → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
                     (λ y → mid y (mul x x))
  ϕᴹ'' x = mid-l-ucontinuous (mul x x)
  ϕᴹ : f-ucontinuous' (ι 𝟛ᴺ-ClosenessSpace)
         (FunPoints-PseudoClosenessSpace ⟨ 𝟛ᴺ-ClosenessSpace ⟩
           𝟛ᴺ-ClosenessSpace Ω' v) M 
  ϕᴹ = close-to-close
         𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
         M v ϕᴹ' ϕᴹ'' Ω'
  𝓔S : csearchable 𝓤₀ 𝟛ᴺ-ClosenessSpace
  𝓔S = 𝟛ᴺ-csearchable {𝓤₀}
  reg : regressor
          𝟛ᴺ-ClosenessSpace
          (FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace Ω' v)
  reg = p-regressor 𝟛ᴺ-ClosenessSpace
          (FunPoints-PseudoClosenessSpace 𝟛ᴺ
            𝟛ᴺ-ClosenessSpace Ω' v)
          𝟛ᴺ-csearchable ε
  ω = M (reg M ϕᴹ Ω')

perfect-regression-test-param-only : {n : ℕ} → ℕ → Vec 𝟛ᴺ n → 𝟛ᴺ
perfect-regression-test-param-only {n} ε v
 = reg M ϕᴹ Ω'
 where
  M : 𝟛ᴺ → (𝟛ᴺ → 𝟛ᴺ)
  M y = λ x → mid y (mul x x)
  k : 𝟛ᴺ
  k = 1/3𝟛ᴺ
  Ω' = M k -- Ω(x) ≔ (1/3 + x²) / 2
  𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace
   = FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace Ω' v
  ϕᴹ' : (y : 𝟛ᴺ) → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
                     (λ x → mid y (mul x x))
  ϕᴹ' y = f-ucontinuous-comp
            𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
            (λ x → mul x x) (mid y)
            mul-b-ucontinuous (mid-r-ucontinuous y)
  ϕᴹ'' : (x : 𝟛ᴺ) → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
                     (λ y → mid y (mul x x))
  ϕᴹ'' x = mid-l-ucontinuous (mul x x)
  ϕᴹ : f-ucontinuous' (ι 𝟛ᴺ-ClosenessSpace)
         (FunPoints-PseudoClosenessSpace ⟨ 𝟛ᴺ-ClosenessSpace ⟩
           𝟛ᴺ-ClosenessSpace Ω' v) M 
  ϕᴹ = close-to-close
         𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
         M v ϕᴹ' ϕᴹ'' k
  𝓔S : csearchable 𝓤₀ 𝟛ᴺ-ClosenessSpace
  𝓔S = 𝟛ᴺ-csearchable {𝓤₀}
  reg : regressor
          𝟛ᴺ-ClosenessSpace
          (FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace Ω' v)
  reg = p-regressor 𝟛ᴺ-ClosenessSpace
          (FunPoints-PseudoClosenessSpace 𝟛ᴺ
            𝟛ᴺ-ClosenessSpace Ω' v)
          𝟛ᴺ-csearchable ε
-}
{-
-- Move to Chapter 3
id-ucontinuous : (X : ClosenessSpace 𝓤)
               → f-ucontinuous X X id
id-ucontinuous X ε = ε , λ _ _ → id

simpler-perfect-regression-test : {n : ℕ} → ℕ → Vec 𝟛ᴺ n → (𝟛ᴺ → 𝟛ᴺ)
simpler-perfect-regression-test {n} ε v
 = M (reg M ϕᴹ Ω')
 where
  M : 𝟛ᴺ → (𝟛ᴺ → 𝟛ᴺ)
  M = mid
  k : 𝟛ᴺ
  k = 1/3𝟛ᴺ
  Ω' = M k -- Ω(x) ≔ (1/3 + x) / 2
  𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace
   = FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace Ω' v
  ϕᴹ' : (y : 𝟛ᴺ) → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
                     (λ x → mid y x)
  ϕᴹ' y = f-ucontinuous-comp
            𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
            id (mid y)
            (id-ucontinuous 𝟛ᴺ-ClosenessSpace) (mid-r-ucontinuous y)
  ϕᴹ'' : (x : 𝟛ᴺ) → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
                     (λ y → mid y x)
  ϕᴹ'' x = mid-l-ucontinuous x
  ϕᴹ : f-ucontinuous' (ι 𝟛ᴺ-ClosenessSpace)
         (FunPoints-PseudoClosenessSpace ⟨ 𝟛ᴺ-ClosenessSpace ⟩
           𝟛ᴺ-ClosenessSpace Ω' v) M 
  ϕᴹ = close-to-close
         𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
         M v ϕᴹ' ϕᴹ'' k
  𝓔S : csearchable 𝓤₀ 𝟛ᴺ-ClosenessSpace
  𝓔S = 𝟛ᴺ-csearchable {𝓤₀}
  reg : regressor
          𝟛ᴺ-ClosenessSpace
          (FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace Ω' v)
  reg = p-regressor 𝟛ᴺ-ClosenessSpace
          (FunPoints-PseudoClosenessSpace 𝟛ᴺ
            𝟛ᴺ-ClosenessSpace Ω' v)
          𝟛ᴺ-csearchable ε
-}
{-
preg-test-eq : ℕ → (𝟛ᴺ → 𝟛ᴺ)
preg-test-eq n = simpler-perfect-regression-test n endpoints
-}

    

{-λ y₁ y₂ Cϵy₁y₂ n n⊏ε
 → decidable-𝟚₁ (discrete-decidable-seq 𝟚-is-discrete _ _ (succ n))
     λ i i<sn → γ y₁ y₂ Cϵy₁y₂ i
       (<-≤-trans i (succ n) ϵ i<sn (⊏-gives-< n ϵ n⊏ε))
 where
  c = pr₁ (pr₂ Y)
  γ : (y₁ y₂ : ⟪ Y ⟫) → C' Y ϵ y₁ y₂ → (pr₁ (c Ω y₁) ∼ⁿ pr₁ (c Ω y₂)) ϵ
  γ y₁ y₂ Cϵy₁y₂ n n<ϵ with C'-decidable Y ϵ Ω y₁
  ... | inl CϵΩy₁ = CϵΩy₁ n (<-gives-⊏ n ϵ n<ϵ) ∙ {!!}
  ... | inr x = {!!} -}

{-
regression-opt' : {n : ℕ} → ℕ → Vec 𝟛ᴺ n → 𝟛ᴺ
regression-opt' ε v
 = pr₁ (optimisation-convergence 𝟛ᴺ-ClosenessSpace
             𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace (repeat O) 𝟛ᴺ-totally-bounded
             M Ω' ϕᴹ ε)
 where
  M : 𝟛ᴺ → (𝟛ᴺ → 𝟛ᴺ)
  M y x = mid y x
  Ω' = mid (repeat O) -- Ω(x) ≔ (1/3 + x) / 2
  𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace
   = FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace Ω' v
  ϕᴹ' : f-ucontinuous
          (×-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace)
          𝟛ᴺ-ClosenessSpace (uncurry (λ y x → mid y x))
  ϕᴹ' = seq-f-ucontinuous²-to-closeness
          𝟛-is-discrete 𝟛-is-discrete 𝟛-is-discrete
          (λ y x → mid y x)
          mid-ucontinuous' {-
          (seq-f-ucontinuous²¹-comp-left mid neg
            mid-ucontinuous' neg-ucontinuous') -}
  ϕᴹ : f-ucontinuous' (ι 𝟛ᴺ-ClosenessSpace) 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace
         (λ y x → mid y x)
  ϕᴹ = close-to-close'
         𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
         (λ y x → mid y x) Ω' v ϕᴹ'
  ϕᶜ : f-ucontinuous' 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace (ι ℕ∞-ClosenessSpace)
         (pr₁ (pr₂ 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace) Ω')
  ϕᶜ = allofthemare 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace Ω'
-}
{-
regression-opt-example : ℕ → 𝟛ᴺ
regression-opt-example n = regression-opt' n endpoints 

run = Seq-to-Vec
-}
```



