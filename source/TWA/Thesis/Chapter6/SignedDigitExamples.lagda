Todd Waugh Ambridge, January 2024

\begin{code}
{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan
open import NotionsOfDecidability.Complemented
open import UF.Subsingletons
open import UF.FunExt
open import MLTT.SpartanList hiding (_∷_;⟨_⟩;[_])

open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter2.Vectors
open import TWA.Thesis.Chapter5.SignedDigit

module TWA.Thesis.Chapter6.SignedDigitExamples
  (fe : FunExt) (pe : PropExt) where

open import TWA.Thesis.Chapter3.ClosenessSpaces fe
 hiding (decidable-predicate;decidable-uc-predicate)
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe
open import TWA.Thesis.Chapter3.SearchableTypes fe
open import TWA.Thesis.Chapter4.ApproxOrder fe
open import TWA.Thesis.Chapter4.ParametricRegression fe
open import TWA.Thesis.Chapter6.SequenceContinuity fe
open import TWA.Thesis.Chapter6.SignedDigitContinuity fe
open import TWA.Thesis.Chapter6.SignedDigitSearch fe pe
open import TWA.Thesis.Chapter6.SignedDigitOrder fe
\end{code}

## Representations we will use

\begin{code}
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
-1𝟛ᴺ   = -1𝟚ᴺ   ↑
-1/2𝟛ᴺ = -1/2𝟚ᴺ ↑
O𝟛ᴺ    = O𝟚ᴺ    ↑
1/4𝟛ᴺ  = 1/4𝟚ᴺ  ↑
1/3𝟛ᴺ  = 1/3𝟚ᴺ  ↑
1/2𝟛ᴺ  = 1/2𝟚ᴺ  ↑
1𝟛ᴺ    = 1𝟚ᴺ    ↑

_/2 _/4 : 𝟛ᴺ → 𝟛ᴺ
x /2 = mid x (repeat O)
x /4 = (x /2) /2 /2
\end{code}

## Search examples

\begin{code}
module Search-Example1 where

 predicate : ℕ → decidable-uc-predicate 𝓤₀ 𝟛ᴺ-ClosenessSpace
 predicate ϵ
  = approx-order-f-uc-predicate-l 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
      (λ x → mid (neg x) (repeat O))
      (f-ucontinuous-comp
         𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
         neg (λ x → mid x (repeat O))
         neg-ucontinuous (mid-l-ucontinuous (repeat O)))
      _≤ⁿ𝟛ᴺ_ ≤ⁿ𝟛ᴺ-is-approx-order ϵ 1/4𝟛ᴺ

 search-test-tb : ℕ → 𝟛ᴺ
 search-test-tb  ϵ = pr₁ (𝟛ᴺ-csearchable-tb (predicate ϵ))

 search-test : ℕ → 𝟛ᴺ
 search-test     ϵ = pr₁ (𝟛ᴺ-csearchable (predicate ϵ))

 search-test-tb' : ℕ → 𝟚ᴺ
 search-test-tb' ϵ = pr₁ (𝟚ᴺ-csearchable-tb (↑-pred (predicate ϵ)))

 search-test' : ℕ → 𝟚ᴺ
 search-test'    ϵ = pr₁ (𝟚ᴺ-csearchable (↑-pred (predicate ϵ)))

module Search-Example2 where

 predicate : ℕ → decidable-uc-predicate 𝓤₀ 𝟛ᴺ-ClosenessSpace
 predicate ϵ
  = C-f-decidable-uc-predicate-l 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
      (λ x → mul x x)
      (seq-f-ucontinuous¹-to-closeness 𝟛-is-discrete 𝟛-is-discrete
        (λ x → mul x x) (seq-f-ucontinuous²-both mul mul-ucontinuous'))
      ϵ 1/2𝟛ᴺ

 search-test-tb : ℕ → 𝟛ᴺ
 search-test-tb  ϵ = pr₁ (𝟛ᴺ-csearchable-tb (predicate ϵ))

 search-test : ℕ → 𝟛ᴺ
 search-test     ϵ = pr₁ (𝟛ᴺ-csearchable (predicate ϵ))

 search-test-tb' : ℕ → 𝟚ᴺ
 search-test-tb' ϵ = pr₁ (𝟚ᴺ-csearchable-tb (↑-pred (predicate ϵ)))

 search-test' : ℕ → 𝟚ᴺ
 search-test'    ϵ = pr₁ (𝟚ᴺ-csearchable (↑-pred (predicate ϵ)))

module Search-Example3 where

 predicate : ℕ → decidable-uc-predicate 𝓤₀ 𝟛ᴺ×𝟛ᴺ-ClosenessSpace
 predicate ϵ
  = C-f-decidable-uc-predicate-l 𝟛ᴺ×𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
      (uncurry mid) mid-ucontinuous ϵ O𝟛ᴺ

 search-test-tb : ℕ → 𝟛ᴺ × 𝟛ᴺ
 search-test-tb  ϵ = pr₁ (𝟛ᴺ×𝟛ᴺ-csearchable-tb (predicate ϵ))

 search-test-tb' : ℕ → 𝟚ᴺ × 𝟚ᴺ
 search-test-tb' ϵ = pr₁ (𝟚ᴺ×𝟚ᴺ-csearchable-tb (⤊-pred (predicate ϵ)))

 search-test : ℕ → 𝟛ᴺ × 𝟛ᴺ
 search-test     ϵ = pr₁ (𝟛ᴺ×𝟛ᴺ-csearchable (predicate ϵ))

 search-test' : ℕ → 𝟚ᴺ × 𝟚ᴺ
 search-test'    ϵ = pr₁ (𝟚ᴺ×𝟚ᴺ-csearchable (⤊-pred (predicate ϵ)))
\end{code}

## Optimisation examples

\begin{code}
module Optimisation-Example1 where

 opt-test : ℕ → 𝟛ᴺ
 opt-test ϵ = pr₁ (𝟛ᴺ→𝟛ᴺ-global-opt neg neg-ucontinuous ϵ)

 opt-test' : ℕ → 𝟚ᴺ
 opt-test' ϵ
  = pr₁ (𝟚ᴺ→𝟛ᴺ-global-opt (neg ∘ _↑)
      (f-ucontinuous-comp
         𝟚ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
         _↑ neg
         ↑-ucontinuous neg-ucontinuous) ϵ)

module Optimisation-Example2 where

 opt-test : ℕ → 𝟛ᴺ
 opt-test ϵ = pr₁ (𝟛ᴺ→𝟛ᴺ-global-opt (λ x → mul x x)
                (seq-f-ucontinuous¹-to-closeness
                  𝟛-is-discrete 𝟛-is-discrete
                  (λ x → mul x x)
                  (seq-f-ucontinuous²-both mul mul-ucontinuous'))
                ϵ)

 opt-test' : ℕ → 𝟚ᴺ
 opt-test' ϵ
  = pr₁ (𝟚ᴺ→𝟛ᴺ-global-opt ((λ x → mul x x) ∘ _↑)
      (f-ucontinuous-comp
         𝟚ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
         _↑ (λ x → mul x x)
         ↑-ucontinuous
         (seq-f-ucontinuous¹-to-closeness
           𝟛-is-discrete 𝟛-is-discrete
           (λ x → mul x x)
           (seq-f-ucontinuous²-both mul mul-ucontinuous'))) ϵ)
\end{code}

## Regression examples

\begin{code}
module Regression-Example
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
  = Least-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace f observations

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
 
module Regression-ExampleDistortionProne
 (X : ClosenessSpace 𝓤)
 (tb : totally-bounded X 𝓥') 
 (S : csearchable 𝓤₀ X)
 (M : ⟨ X ⟩ → (𝟛ᴺ → 𝟛ᴺ))
 (𝓞 : 𝟛ᴺ → 𝟛ᴺ)
 (Ψ : (𝟛ᴺ → 𝟛ᴺ) → (𝟛ᴺ → 𝟛ᴺ))
 {n : ℕ} (observations : Vec 𝟛ᴺ n)
 (ϕᴹ : (y : 𝟛ᴺ) → f-ucontinuous X 𝟛ᴺ-ClosenessSpace λ x → M x y)
 where

 open Regression-Example X X id (id-ucontinuous X) tb S M (Ψ 𝓞)
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

 ϕᴹ : (y : 𝟛ᴺ)
    → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
       (λ x → mid (neg x) y)
 ϕᴹ y = f-ucontinuous-comp 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
         𝟛ᴺ-ClosenessSpace neg (λ x → mid x y)
         neg-ucontinuous
         (seq-f-ucontinuous¹-to-closeness
         𝟛-is-discrete 𝟛-is-discrete
         (λ x → mid x y)
         (seq-f-ucontinuous²-left mid mid-ucontinuous' y))
 
 open Regression-Example
   𝟛ᴺ-ClosenessSpace 𝟚ᴺ-ClosenessSpace
   _↑ ↑-ucontinuous
   𝟚ᴺ-totally-bounded 𝟚ᴺ-csearchable-tb
   M 𝓞
   observations ϕᴹ
   public

 Ψ : (𝟛ᴺ → 𝟛ᴺ) → (𝟛ᴺ → 𝟛ᴺ)
 Ψ f x = mid x (x /4)

 open Regression-ExampleDistortionProne
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
 
 open Regression-Example
   𝟛ᴺ×𝟛ᴺ-ClosenessSpace 𝟚ᴺ×𝟚ᴺ-ClosenessSpace
   _⤊ ⤊-ucontinuous
   𝟚ᴺ×𝟚ᴺ-totally-bounded 𝟚ᴺ×𝟚ᴺ-csearchable-tb
   M 𝓞 observations ϕᴹ
   public

 open Regression-ExampleDistortionProne
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

 open Regression-Example
   𝟛ᴺ×𝟛ᴺ-ClosenessSpace 𝟚ᴺ×𝟚ᴺ-ClosenessSpace
   _⤊ ⤊-ucontinuous
   𝟚ᴺ×𝟚ᴺ-totally-bounded 𝟚ᴺ×𝟚ᴺ-csearchable-tb
   M 𝓞 observations ϕᴹ
   public

module Regression-Example1a-Optimisation where

 open Regression-Example1a

 regressed-parameter : ℕ → 𝟛ᴺ
 regressed-parameter = _↑ ∘ (opt 𝓞)

 regressed-function : ℕ → (𝟛ᴺ → 𝟛ᴺ)
 regressed-function = M ∘ regressed-parameter

module Regression-Example1a-SearchDistortionFree where

 open Regression-Example1a

 regressed-parameter : ℕ → 𝟛ᴺ
 regressed-parameter = _↑ ∘ (reg𝓞)

 regressed-function : ℕ → (𝟛ᴺ → 𝟛ᴺ)
 regressed-function = M ∘ regressed-parameter

module Regression-Example1a-SearchDistortionProne where

 open Regression-Example1a

 regressed-parameter : ℕ → 𝟛ᴺ
 regressed-parameter = regΨ𝓞

 regressed-function : ℕ → (𝟛ᴺ → 𝟛ᴺ)
 regressed-function = M ∘ regressed-parameter

module Regression-Example1a-OptimisationDistortionProne where

 open Regression-Example1a

 regressed-parameter : ℕ → 𝟛ᴺ
 regressed-parameter = _↑ ∘ opt (Ψ 𝓞)

 regressed-function : ℕ → (𝟛ᴺ → 𝟛ᴺ)
 regressed-function = M ∘ regressed-parameter

module Regression-Example1b-DistortionProne where

 open Regression-Example1b

 regressed-parameter : ℕ → 𝟛ᴺ × 𝟛ᴺ
 regressed-parameter = regΨ𝓞

 regressed-function : ℕ → (𝟛ᴺ → 𝟛ᴺ)
 regressed-function = M ∘ regressed-parameter

module Regression-Example2-SearchDistortionFree where

 open Regression-Example2

 regressed-parameter : ℕ → 𝟛ᴺ × 𝟛ᴺ
 regressed-parameter ϵ = α ↑ , β ↑
  where
   αβ = reg𝓞 ϵ
   α = pr₁ αβ
   β = pr₂ αβ

 regressed-function : ℕ → (𝟛ᴺ → 𝟛ᴺ)
 regressed-function = M ∘ regressed-parameter
\end{code}
