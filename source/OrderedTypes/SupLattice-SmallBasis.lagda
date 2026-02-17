Ian Ray, started: 2023-09-12 - updated: 2024-02-05

We define the notion of a small basis for a suplattice as well as some
boiler plate. This consists of a type B and a map β : B → L. In a sense to be
made precise we say the pair B and q generate the suplattice. This notion
is crucial for the development of predicative order theory.

This notion of a basis was motivated by the set theoretic formulation due to
Curi (see http://doi.org/10.1090/proc/12569) and can be compared with a similar
notion for Domains due to Tom de Jong (see DomainTheory.BasisAndContinuity).

A suplattice L that has suprema for family of size 𝓥 has a basis if there is a
type B : 𝓥 and map β : B → L such that
  β b ≤ x is 𝓥 small
and
  x = ⋁ ↓ᴮ x
for all x.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.Size

module OrderedTypes.SupLattice-SmallBasis
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.Frame pt fe hiding (⟨_⟩ ; join-of)
open import Slice.Family
open import OrderedTypes.SupLattice pt fe

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

\begin{code}

module _
        {𝓤 𝓣 𝓥 : Universe}
        {B : 𝓥 ̇ }
        (L : Sup-Lattice 𝓤 𝓣 𝓥)
        (β : B → ⟨ L ⟩)
       where

 private
  _≤_ : ⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓣
  _≤_ = order-of L

  ⋁_ : Fam 𝓥 ⟨ L ⟩ → ⟨ L ⟩
  ⋁_ = join-of L

 open Joins _≤_

 ↓ᴮ : ⟨ L ⟩ → 𝓣 ⊔ 𝓥 ̇
 ↓ᴮ x = Σ b ꞉ B , (β b ≤ x) holds

 ↓ᴮ-to-base : (x : ⟨ L ⟩) → ↓ᴮ x → B
 ↓ᴮ-to-base x = pr₁

 ↓ᴮ-inclusion : (x : ⟨ L ⟩) → ↓ᴮ x → ⟨ L ⟩
 ↓ᴮ-inclusion x = β ∘ ↓ᴮ-to-base x

\end{code}

It is worth mentioning the ↓ᴮ-inclusion need not be an injection as β is not.

Now we define is-small-basis as a record type and proceed to write some
boiler plate that will allow us to use a small basis with greater efficiency.

\begin{code}

 record is-basis : 𝓤 ⊔ 𝓣 ⊔ 𝓥 ⁺ ̇ where
  field
   ≤-is-small : (x : ⟨ L ⟩) (b : B) → ((β b ≤ x) holds) is 𝓥 small
   ↓-is-sup : (x : ⟨ L ⟩) → (x is-lub-of (↓ᴮ x , ↓ᴮ-inclusion x)) holds

  is-upper-bound-↓ : (x : ⟨ L ⟩)
                   → (x is-an-upper-bound-of (↓ᴮ x , ↓ᴮ-inclusion x)) holds
  is-upper-bound-↓ x = pr₁ (↓-is-sup x)

  is-least-upper-bound-↓ : (x : ⟨ L ⟩)
                         → ((u' , _) : upper-bound (↓ᴮ x , ↓ᴮ-inclusion x))
                         → (x ≤ u') holds
  is-least-upper-bound-↓ x = pr₂ (↓-is-sup x)

  _≤ᴮ_ : (b : B) → (x : ⟨ L ⟩) → 𝓥 ̇
  b ≤ᴮ x = (resized ((β b ≤ x) holds)) (≤-is-small x b)

  ≤ᴮ-≃-≤ : {b : B} {x : ⟨ L ⟩} → (b ≤ᴮ x) ≃ ((β b) ≤ x) holds
  ≤ᴮ-≃-≤ {b} {x} = (resizing-condition) (≤-is-small x b)

  ≤ᴮ-to-≤ : {b : B} {x : ⟨ L ⟩} → (b ≤ᴮ x) → ((β b) ≤ x) holds
  ≤ᴮ-to-≤ = ⌜ ≤ᴮ-≃-≤ ⌝

  ≤-to-≤ᴮ : {b : B} {x : ⟨ L ⟩} → ((β b) ≤ x) holds → (b ≤ᴮ x)
  ≤-to-≤ᴮ = ⌜ ≤ᴮ-≃-≤ ⌝⁻¹

  ≤ᴮ-is-prop-valued : {b : B} {x : ⟨ L ⟩} → is-prop (b ≤ᴮ x)
  ≤ᴮ-is-prop-valued {b} {x} =
   equiv-to-prop ≤ᴮ-≃-≤ (holds-is-prop ((β b) ≤ x))

  small-↓ᴮ : ⟨ L ⟩ → 𝓥 ̇
  small-↓ᴮ x = Σ b ꞉ B , b ≤ᴮ x

  small-↓ᴮ-inclusion : (x : ⟨ L ⟩) → small-↓ᴮ x → ⟨ L ⟩
  small-↓ᴮ-inclusion x = β ∘ pr₁

  small-↓ᴮ-≃-↓ᴮ : {x : ⟨ L ⟩} → small-↓ᴮ x ≃ ↓ᴮ x
  small-↓ᴮ-≃-↓ᴮ {x} = Σ-cong (λ _ → ≤ᴮ-≃-≤)

  ↓ᴮ-is-small : {x : ⟨ L ⟩} → ↓ᴮ x is 𝓥 small
  ↓ᴮ-is-small {x} = (small-↓ᴮ x , small-↓ᴮ-≃-↓ᴮ {x})

  is-supᴮ' : (x : ⟨ L ⟩) → x ＝ ⋁ (small-↓ᴮ x , small-↓ᴮ-inclusion x)
  is-supᴮ' x = reindexing-along-equiv-＝-sup
                L small-↓ᴮ-≃-↓ᴮ (↓ᴮ-inclusion x)
                x (⋁ (small-↓ᴮ x , small-↓ᴮ-inclusion x)) (↓-is-sup x)
                (join-is-lub-of L (small-↓ᴮ x , small-↓ᴮ-inclusion x))

  is-supᴮ : (x : ⟨ L ⟩)
          → (x is-lub-of (small-↓ᴮ x , small-↓ᴮ-inclusion x)) holds
  is-supᴮ x =
   transport (λ z → (z is-lub-of (small-↓ᴮ x , small-↓ᴮ-inclusion x)) holds)
             (is-supᴮ' x ⁻¹)
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
