Ian Ray 29\01\2024

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Hedberg
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.PropTrunc
open import UF.Retracts
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.Size
open import UF.SmallnessProperties
open import UF.UniverseEmbedding

module OrderedTypes.SupLattice-SmallBasis
       (pt : propositional-truncations-exist)
       (fe : Fun-Ext)
       (fe' : FunExt)
       (pe : Prop-Ext)
        where

open import Locales.Frame pt fe hiding (⟨_⟩ ; join-of)
open import Slice.Family
open import UF.ImageAndSurjection pt
open import OrderedTypes.SupLattice pt fe fe' pe

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

We define the notion of a small basis for a sup-lattice as well as some
boiler plate. This consists of a type B and a map q : B → L. In a sense to be
made precise we say the pair B and q generate the sup-lattice. This notion
is crucial for the development of predicative order theory.

\begin{code}

module small-basis {𝓤 𝓦 𝓥 : Universe}
                   {B : 𝓥  ̇}
                   (L : Sup-Lattice 𝓤 𝓦 𝓥)
                   (β : B → ⟨ L ⟩)
                    where

 _≤_ : ⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓦
 _≤_ = order-of L

 ⋁_ : Fam 𝓥 ⟨ L ⟩ → ⟨ L ⟩
 ⋁_ = join-of L

 open Joins _≤_

 ↓ᴮ : ⟨ L ⟩ → 𝓦 ⊔ 𝓥  ̇
 ↓ᴮ x = Σ b ꞉ B , (β b ≤ x) holds

 ↓ᴮ-to-base : (x : ⟨ L ⟩) → ↓ᴮ x → B
 ↓ᴮ-to-base x = pr₁

 ↓ᴮ-inclusion : (x : ⟨ L ⟩) → ↓ᴮ x → ⟨ L ⟩
 ↓ᴮ-inclusion x = β ∘ ↓ᴮ-to-base x

 is-small-basis : 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⁺  ̇
 is-small-basis = (x : ⟨ L ⟩)
                → ((b : B) → ((β b ≤ x) holds) is 𝓥 small)
                × ((x is-lub-of (↓ᴮ x , ↓ᴮ-inclusion x)) holds)

 module small-basis-facts (h : is-small-basis) where

  ≤-is-small : (x : ⟨ L ⟩) (b : B) → ((β b ≤ x) holds) is 𝓥 small
  ≤-is-small x b = pr₁ (h x) b

  is-sup-↓ : (x : ⟨ L ⟩) → (x is-lub-of (↓ᴮ x , ↓ᴮ-inclusion x)) holds
  is-sup-↓ x = pr₂ (h x)

  is-upper-bound-↓ : (x : ⟨ L ⟩)
                   → (x is-an-upper-bound-of (↓ᴮ x , ↓ᴮ-inclusion x)) holds
  is-upper-bound-↓ x = pr₁ (is-sup-↓ x)

  is-least-upper-bound-↓ : (x : ⟨ L ⟩)
                         → ((u' , _) : upper-bound (↓ᴮ x , ↓ᴮ-inclusion x))
                         → (x ≤ u') holds
  is-least-upper-bound-↓ x = pr₂ (is-sup-↓ x)

  _≤ᴮ_ : (b : B) → (x : ⟨ L ⟩) → 𝓥  ̇
  b ≤ᴮ x = (resized ((β b ≤ x) holds)) (≤-is-small x b)

  _≤ᴮ_-≃-_≤_ : {b : B} {x : ⟨ L ⟩} → (b ≤ᴮ x) ≃ ((β b) ≤ x) holds
  _≤ᴮ_-≃-_≤_ {b} {x} = (resizing-condition) (≤-is-small x b)

  _≤ᴮ_-to-_≤_ : {b : B} {x : ⟨ L ⟩} → (b ≤ᴮ x) → ((β b) ≤ x) holds
  _≤ᴮ_-to-_≤_ = ⌜ _≤ᴮ_-≃-_≤_ ⌝

  _≤_-to-_≤ᴮ_ : {b : B} {x : ⟨ L ⟩} → ((β b) ≤ x) holds → (b ≤ᴮ x)
  _≤_-to-_≤ᴮ_ = ⌜ _≤ᴮ_-≃-_≤_ ⌝⁻¹

  _≤ᴮ_-is-prop-valued : {b : B} {x : ⟨ L ⟩} → is-prop (b ≤ᴮ x)
  _≤ᴮ_-is-prop-valued {b} {x} =
   equiv-to-prop _≤ᴮ_-≃-_≤_ (holds-is-prop ((β b) ≤ x))

  small-↓ᴮ : ⟨ L ⟩ → 𝓥  ̇
  small-↓ᴮ x = Σ b ꞉ B , b ≤ᴮ x

  small-↓ᴮ-inclusion : (x : ⟨ L ⟩) → small-↓ᴮ x → ⟨ L ⟩
  small-↓ᴮ-inclusion x = β ∘ pr₁

  small-↓ᴮ-≃-↓ᴮ : {x : ⟨ L ⟩} → small-↓ᴮ x ≃ ↓ᴮ x
  small-↓ᴮ-≃-↓ᴮ {x} = Σ-cong (λ _ → _≤ᴮ_-≃-_≤_)

  ↓ᴮ-is-small : {x : ⟨ L ⟩} → ↓ᴮ x is 𝓥 small
  ↓ᴮ-is-small {x} = (small-↓ᴮ x , small-↓ᴮ-≃-↓ᴮ {x})

  is-sup'ᴮ : (x : ⟨ L ⟩) → x ＝ ⋁ (small-↓ᴮ x , small-↓ᴮ-inclusion x)
  is-sup'ᴮ x = reindexing-along-equiv-＝-sup
                 L small-↓ᴮ-≃-↓ᴮ (↓ᴮ-inclusion x)
                 x (⋁ (small-↓ᴮ x , small-↓ᴮ-inclusion x)) (is-sup-↓ x)
                 (join-is-lub-of L (small-↓ᴮ x , small-↓ᴮ-inclusion x))

  is-supᴮ : (x : ⟨ L ⟩)
          → (x is-lub-of (small-↓ᴮ x , small-↓ᴮ-inclusion x)) holds
  is-supᴮ x =
    transport (λ z → (z is-lub-of (small-↓ᴮ x , small-↓ᴮ-inclusion x)) holds)
              (is-sup'ᴮ x ⁻¹)
              (join-is-lub-of L ((small-↓ᴮ x , small-↓ᴮ-inclusion x)))

  is-upper-boundᴮ : (x : ⟨ L ⟩)
                  → (x is-an-upper-bound-of
                       (small-↓ᴮ x , small-↓ᴮ-inclusion x)) holds
  is-upper-boundᴮ x = pr₁ (is-supᴮ x)

  is-least-upper-boundᴮ : (x : ⟨ L ⟩)
                        → ((u' , _) : upper-bound
                                      (small-↓ᴮ x , small-↓ᴮ-inclusion x))
                        → (x ≤ u') holds
  is-least-upper-boundᴮ x = pr₂ (is-supᴮ x)

\end{code}
