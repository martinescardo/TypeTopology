\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import NotionsOfDecidability.Complemented
open import TypeTopology.DiscreteAndSeparated
open import Notation.Order
open import Naturals.Order
open import Naturals.Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Quotient
open import UF.Miscelanea
open import MLTT.Two-Properties
open import MLTT.Plus-Properties
open import UF.Equiv

module Thesis.Chapter4.ApproxOrder (fe : FunExt) where

open import Thesis.Chapter2.FiniteDiscrete
open import Thesis.Chapter3.ClosenessSpaces fe
open import Thesis.Chapter3.ClosenessSpaces-Examples fe
open import Thesis.Chapter3.SearchableTypes fe
open import CoNaturals.GenericConvergentSequence
  renaming (ℕ-to-ℕ∞ to _↑
         ; Zero-smallest to zero-minimal
         ; ∞-largest to ∞-maximal)

-- Definition 4.1.4
is-preorder : {X : 𝓤  ̇ } → (X → X → 𝓦  ̇ ) → 𝓤 ⊔ 𝓦  ̇ 
is-preorder _≤_ = reflexive _≤_
                × transitive _≤_
                × is-prop-valued _≤_

-- Definition 4.1.5
is-linear-order : {X : 𝓤  ̇ } → (X → X → 𝓦  ̇ ) → 𝓤 ⊔ 𝓦  ̇
is-linear-order {_} {_} {X} _≤_
 = is-preorder _≤_
 × ((x y : X) → (x ≤ y) + (y ≤ x))

is-strict-order : {X : 𝓤  ̇ } → (X → X → 𝓦  ̇ ) → 𝓤 ⊔ 𝓦  ̇ 
is-strict-order {_} {_} {X} _<_
 = ((x : X) → ¬ (x < x))
 × transitive _<_
 × ((x y : X) → x < y → ¬ (y < x))
 × is-prop-valued _<_

-- Lemma 4.1.13
-- TODO

-- Definition 4.1.14
is-approx-order : (X : ClosenessSpace 𝓤)
                → (_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
                → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ )
                → 𝓤 ⊔ 𝓦 ⊔ 𝓦'  ̇
is-approx-order X _≤_ _≤ⁿ_
 = is-preorder _≤_
 × ((ϵ : ℕ) → is-linear-order (λ x y → (x ≤ⁿ y) ϵ))
 × ((ϵ : ℕ) (x y : ⟨ X ⟩) →   C X ϵ x y → (x ≤ⁿ y) ϵ)
 × ((ϵ : ℕ) (x y : ⟨ X ⟩) → ¬ C X ϵ x y → (x ≤ⁿ y) ϵ ⇔ x ≤ y)

-- Make clearer in thesis:
approx-order-refl : (X : ClosenessSpace 𝓤)
                  → (_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
                  → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ )
                  → is-approx-order X _≤_ _≤ⁿ_
                  → (ϵ : ℕ) (x : ⟨ X ⟩) → (x ≤ⁿ x) ϵ
approx-order-refl X _≤_ _≤ⁿ_ (p , l , c , a) ϵ x
 = c ϵ x x (C-refl X ϵ x)

approx-order-trans : (X : ClosenessSpace 𝓤)
                   → (_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
                   → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ )
                   → is-approx-order X _≤_ _≤ⁿ_
                   → (ϵ : ℕ) (x y z : ⟨ X ⟩)
                   → (x ≤ⁿ y) ϵ → (y ≤ⁿ z) ϵ → (x ≤ⁿ z) ϵ
approx-order-trans X _≤_ _≤ⁿ_ (p , l , c , a) ϵ
 = (pr₁ ∘ pr₂ ∘ pr₁) (l ϵ)

approx-order-linear : (X : ClosenessSpace 𝓤)
                    → (_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
                    → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ )
                    → is-approx-order X _≤_ _≤ⁿ_
                    → (ϵ : ℕ) (x y : ⟨ X ⟩)
                    → (x ≤ⁿ y) ϵ + (y ≤ⁿ x) ϵ
approx-order-linear X _≤_ _≤ⁿ_ (_ , l , _ , _) ϵ
 = pr₂ (l ϵ)

-- Lemma 4.1.15
apart-total : {X : ClosenessSpace 𝓤}
            → (_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
            → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ )
            → is-approx-order X _≤_ _≤ⁿ_
            → (ϵ : ℕ) (x y : ⟨ X ⟩) 
            → ¬ C X ϵ x y → (x ≤ y) + (y ≤ x)
apart-total {_} {_} {_} {X} _≤_ _≤ⁿ_ (p , l , c , a) ϵ x y ¬Bϵxy
 = Cases (pr₂ (l ϵ) x y)
     (inl ∘ pr₁ (a ϵ x y ¬Bϵxy))
     (inr ∘ pr₁ (a ϵ y x λ Bϵxy → ¬Bϵxy (C-sym X ϵ y x Bϵxy)))

-- Definition 4.1.16
-- TODO

-- Lemma 4.1.17
-- TODO
\end{code}
