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

module TWA.Thesis.Chapter6.ZeroNormalisation
  (fe : FunExt) (pe : PropExt) where

open import TWA.Thesis.Chapter2.FiniteDiscrete
open import TWA.Thesis.Chapter2.Sequences
-- open import TWA.Thesis.Chapter2.Vectors
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
-- open import TWA.Thesis.Chapter6.SignedDigitSearch fe pe
open import Dyadics.Type
open import Naturals.Addition renaming (_+_ to _+'_)
open import Naturals.Multiplication
open import Naturals.Exponentiation

f-1 fO f+1 : ℕ × ℕ → ℕ × ℕ
f-1 (m , n) = m
            , succ n
fO  (m , n) = m +' m +' 2 ℕ^ n
            , succ (succ n)
f+1 (m , n) = m +' 2 ℕ^ n
            , succ n

𝟛ᴺ→ℕ×ℕ' : 𝟛 → 𝟛ᴺ → (ℕ → ℕ × ℕ)
𝟛ᴺ→ℕ×ℕ' _ α 0 = 1 , 0
𝟛ᴺ→ℕ×ℕ' −1 α (succ n) = f-1 (𝟛ᴺ→ℕ×ℕ' (α 0) (α ∘ succ) n)
𝟛ᴺ→ℕ×ℕ'  O α (succ n) = fO  (𝟛ᴺ→ℕ×ℕ' (α 0) (α ∘ succ) n)
𝟛ᴺ→ℕ×ℕ' +1 α (succ n) = f+1 (𝟛ᴺ→ℕ×ℕ' (α 0) (α ∘ succ) n)

𝟛ᴺ→ℕ×ℕ : 𝟛ᴺ → ℕ → ℕ × ℕ
𝟛ᴺ→ℕ×ℕ α = 𝟛ᴺ→ℕ×ℕ' (α 0) (α ∘ succ)

open import Integers.Type
open import Notation.Order
open import Integers.Order
open import TWA.Thesis.Chapter5.BelowAndAbove

𝟛-to-down : (a : 𝟛) → (ℤ → ℤ)
𝟛-to-down −1 = downLeft
𝟛-to-down  O = downMid
𝟛-to-down +1 = downRight

ternary-to-ℤ²-pos' : 𝟛ᴺ → ℤ → (ℕ → ℤ)

ternary-to-ℤ²-pos'' : 𝟛 → 𝟛ᴺ → ℤ → (ℕ → ℤ)
ternary-to-ℤ²-pos'' _ α k 0 = k
ternary-to-ℤ²-pos'' b α k (succ n)
 = ternary-to-ℤ²-pos' α (𝟛-to-down b k) n

ternary-to-ℤ²-pos' α = ternary-to-ℤ²-pos'' (α 0) (α ∘ succ)

ternary-to-ℤ²-pos : 𝟛ᴺ → (ℕ → ℤ)
ternary-to-ℤ²-pos α = ternary-to-ℤ²-pos' α (negsucc 0)

ternary-to-ℤ²' : 𝟛 → 𝟛ᴺ → ℤ → (ℕ → ℤ × ℕ)
ternary-to-ℤ²' b α k n = ternary-to-ℤ²-pos α n , n

ternary-to-ℤ² : 𝟛ᴺ → (ℕ → ℤ × ℕ)
ternary-to-ℤ² α = ternary-to-ℤ²' (α 0) (α ∘ succ) (negsucc 0)

-- 𝟛ᴺ→ℕ×ℕ zα 0 = 1,0   = 1.00  = 1.00  = 1,0 = 𝟛ᴺ→ℕ×ℕ zβ 0
-- 𝟛ᴺ→ℕ×ℕ zα 1 = 3,2   = 0.75  < 1.00  = 2,1 = 𝟛ᴺ→ℕ×ℕ zβ 1
-- 𝟛ᴺ→ℕ×ℕ zα 2 = 6,3   = 0.75  = 0.75  = 3,2 = 𝟛ᴺ→ℕ×ℕ zβ 2
-- 𝟛ᴺ→ℕ×ℕ zα 3 = 10,4  = 0.625 = 0.625 = 5,3 = 𝟛ᴺ→ℕ×ℕ zβ 3

-- ternary-to-ℤ²-pos zα 0 = -1 = -1 = ternary-to-ℤ²-pos zβ 0
-- ternary-to-ℤ²-pos zα 1 = -1 <  0 = ternary-to-ℤ²-pos zβ 1
-- ternary-to-ℤ²-pos zα 2 =  0 =  0 = ternary-to-ℤ²-pos zβ 2
-- ternary-to-ℤ²-pos zα 3 =  0 =  0 = ternary-to-ℤ²-pos zβ 3

_≤ⁿ𝟛ᴺ_ : 𝟛ᴺ → 𝟛ᴺ → ℕ → 𝓤₀ ̇
(x ≤ⁿ𝟛ᴺ y) n = ternary-to-ℤ²-pos x n ≤ ternary-to-ℤ²-pos y n

+1≠O : ¬ (Id {𝓤₀} {𝟛} +1 O)
+1≠O ()

zα zβ : 𝟛ᴺ
zα =  O ∶∶ (+1 ∶∶ repeat −1)
zβ = +1 ∶∶ (repeat      −1)

test-incorrect : (n : ℕ)
               → n > 0
               → (discrete-lexicorder
                      𝟛-is-discrete (finite-strict-order 𝟛-finite)
                      zα zβ)
               × ¬ (discrete-lexicorder
                      𝟛-is-discrete (finite-strict-order 𝟛-finite)
                      zβ zα)
pr₁ (test-incorrect (succ n) _) = inr (0 , (λ _ ()) , ⋆)
pr₂ (test-incorrect (succ n) _) (inl x) = +1≠O (x 0)
pr₂ (test-incorrect (succ n) _) (inr (succ i , zβ∼zα , _))
 = +1≠O (zβ∼zα 0 ⋆)

test-correct : (n : ℕ) → n > 1 → (zα ≤ⁿ𝟛ᴺ zβ) n × (zβ ≤ⁿ𝟛ᴺ zα) n
test-correct (succ (succ n)) _ = ℤ≤-refl _ , ℤ≤-refl _

≤ⁿ𝟛ᴺ-is-linear-order
 : (n : ℕ) → is-linear-order (λ x y → (x ≤ⁿ𝟛ᴺ y) n)
≤ⁿ𝟛ᴺ-is-linear-order n
 = ((λ x → ℤ≤-refl _)
 , (λ x y z → ℤ≤-trans _ _ _)
 , λ x y → ℤ≤-is-prop _ _)
 , λ x y → ℤ-dichotomous _ _

ℤ≤-decidable : (n m : ℤ) → (n ≤ m) + ¬ (n ≤ m)
ℤ≤-decidable n m
 = Cases (ℤ-trichotomous m n)
     (inr ∘ ℤ-less-not-bigger-or-equal m n)
     (inl ∘ ℤ≤-attach n m)

≤ⁿ𝟛ᴺ-is-decidable : (n : ℕ) (x y : 𝟛ᴺ)
                  → is-decidable ((x ≤ⁿ𝟛ᴺ y) n)
≤ⁿ𝟛ᴺ-is-decidable n x y = ℤ≤-decidable _ _

ternary-to-ℤ²-pos'-ucontinuous
 : (ϵ : ℕ) (x y : 𝟛ᴺ)
 → (x ∼ⁿ y) ϵ
 → (k : ℤ)
 → ternary-to-ℤ²-pos' x k ϵ ＝ ternary-to-ℤ²-pos' y k ϵ
ternary-to-ℤ²-pos'-ucontinuous 0 x y x∼y k = refl 
ternary-to-ℤ²-pos'-ucontinuous (succ ϵ) x y x∼y k
 = ap (λ - → ternary-to-ℤ²-pos'' (x 1) (x ∘ succ ∘ succ)
              (𝟛-to-down - k) ϵ)
   (x∼y 0 ⋆)
 ∙ ternary-to-ℤ²-pos'-ucontinuous ϵ (x ∘ succ) (y ∘ succ)
     (x∼y ∘ succ) (𝟛-to-down (y 0) k)

≤ⁿ𝟛ᴺ-closeness : (ϵ : ℕ) (x y : 𝟛ᴺ)
               → C 𝟛ᴺ-ClosenessSpace ϵ x y
               → (x ≤ⁿ𝟛ᴺ y) ϵ
≤ⁿ𝟛ᴺ-closeness ϵ x y Cxy
 = 0 , ternary-to-ℤ²-pos'-ucontinuous ϵ x y
         (C-to-∼ⁿ _ x y ϵ Cxy) (negsucc 0)

≤ⁿ𝟛ᴺ-is-approx-order : is-approx-order' 𝟛ᴺ-ClosenessSpace _≤ⁿ𝟛ᴺ_
≤ⁿ𝟛ᴺ-is-approx-order
 = ≤ⁿ𝟛ᴺ-is-linear-order , ≤ⁿ𝟛ᴺ-is-decidable , ≤ⁿ𝟛ᴺ-closeness

_≤ⁿ𝟛ᴺ'_ : 𝟛ᴺ → 𝟛ᴺ → ℕ → Ω 𝓤₀
(x ≤ⁿ𝟛ᴺ' y) n = (x ≤ⁿ𝟛ᴺ y) n
              , ≤ⁿ-prop 𝟛ᴺ-ClosenessSpace ≤ⁿ𝟛ᴺ-is-approx-order n x y 

{-
open import UF.
PropTrunc

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 _≤𝟛ᴺ_ : 𝟛ᴺ → 𝟛ᴺ → 𝓤₀ ̇
 x ≤𝟛ᴺ y
  = ∃ n ꞉ ℕ
  , ((i : ℕ) → n ≤ i → ternary-to-ℤ²-pos x i ≤ ternary-to-ℤ²-pos y i)

 ≤𝟛ᴺ-is-preorder :
 -}
```
