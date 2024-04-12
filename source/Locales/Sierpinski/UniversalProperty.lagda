--------------------------------------------------------------------------------
title:          Universal property of the Sierpiński locale
author:         Ayberk Tosun
date-started:   2024-03-06
date-completed: 2024-03-09
--------------------------------------------------------------------------------

In this module, we

  1. define the universal property of Sierpiński which amounts to the fact that
     it is the free frame on one generator; and
  2. we prove that the Scott locale of the Sierpiński dcpo satisfies this
     universal property.

This the implementation of a proof sketch communicated to me by Martín Escardó.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons

module Locales.Sierpinski.UniversalProperty
        (𝓤  : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

open import DomainTheory.Basics.Dcpo pt fe 𝓤 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Basics.Pointed pt fe 𝓤
open import DomainTheory.Topology.ScottTopology pt fe 𝓤
open import DomainTheory.Topology.ScottTopologyProperties pt fe
open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Ideal pt fe pe
open import Locales.DistributiveLattice.Properties fe pt
open import Locales.Frame pt fe hiding (is-directed)
open import Locales.ScottLocale.Definition pt fe 𝓤
open import Locales.ScottLocale.Properties pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfScottDomains pt fe sr 𝓤
open import Locales.Sierpinski.Definition 𝓤 pe pt fe sr
open import Locales.Sierpinski.Properties 𝓤 pe pt fe sr
open import Locales.SmallBasis pt fe sr
open import MLTT.Fin hiding (𝟎; 𝟏)
open import MLTT.List hiding ([_])
open import Slice.Family
open import UF.Logic
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)
open ContinuousMaps
open DefnOfScottLocale 𝕊𝓓 𝓤 pe hiding (⊤ₛ)
open DefnOfScottTopology 𝕊𝓓 𝓤
open FrameHomomorphismProperties
open FrameHomomorphisms
open Locale
open PropertiesAlgebraic 𝓤 𝕊𝓓 𝕊𝓓-is-structurally-algebraic
open PropositionalTruncation pt hiding (_∨_)
open ScottLocaleConstruction 𝕊𝓓 hscb pe


\end{code}

\section{The definition of the universal property}

Given a locale S with a chosen open truth : 𝒪(S), S satisfies the universal
property of the Sierpiński locale if

    for any locale X, any open U : 𝒪(X), there exists a continuous map f : X → S
    unique with the property that f(truth) = U.

In other words, this says that the Sierpiński locale is the locale whose
defining frame is the free frame on one generator.

\begin{code}

has-the-universal-property-of-sierpinski : (S : Locale (𝓤 ⁺) 𝓤 𝓤)
                                         → ⟨ 𝒪 S ⟩
                                         → 𝓤 ⁺ ⁺  ̇
has-the-universal-property-of-sierpinski S truth =
 (X : Locale (𝓤 ⁺) 𝓤 𝓤) →
  (U : ⟨ 𝒪 X ⟩) →
   ∃! (f , _) ꞉ (X ─c→ S) , U ＝ f truth

\end{code}

\section{The Scott locale of the Sierpiński dcpo has this universal property}

We denote by `𝒽` the defining frame homomorphism of the continuous map required
for the universal property.

\begin{code}

universal-property-of-sierpinski : has-the-universal-property-of-sierpinski 𝕊 truth
universal-property-of-sierpinski X U = (𝒽 , †) , ‡
 where
  open PosetNotation (poset-of (𝒪 X))
  open PosetReasoning (poset-of (𝒪 X))
  open Joins _≤_

\end{code}

We adopt the convention of using 𝔣𝔯𝔞𝔨𝔱𝔲𝔯 letters for Scott opens.

The frame homomorphism `h : 𝒪(𝕊) → 𝒪(X)` is defined as `h(𝔙) :≡ ⋁ (ℱₓ 𝔙)` where
`ℱₓ 𝔙` denotes the following family.

\begin{code}

  I : ⟨ 𝒪 𝕊 ⟩ → 𝓤  ̇
  I 𝔘 = (⊤ₛ ∈ₛ 𝔘) holds + (⊥ₛ ∈ₛ 𝔘) holds

  α : (𝔙 : ⟨ 𝒪 𝕊 ⟩) → (⊤ₛ ∈ₛ 𝔙) holds + (⊥ₛ ∈ₛ 𝔙) holds → ⟨ 𝒪 X ⟩
  α V (inl _) = U
  α V (inr _) = 𝟏[ 𝒪 X ]

  ℱₓ : ⟨ 𝒪 𝕊 ⟩ → Fam 𝓤 ⟨ 𝒪 X ⟩
  ℱₓ 𝔙 = (I 𝔙 , α 𝔙)

  h : ⟨ 𝒪 𝕊 ⟩ → ⟨ 𝒪 X ⟩
  h 𝔙 = ⋁[ 𝒪 X ] ℱₓ 𝔙

\end{code}

It is easy to see that this map is monotone.

\begin{code}

  𝓂 : is-monotonic (poset-of (𝒪 𝕊)) (poset-of (𝒪 X)) h holds
  𝓂 (V₁ , V₂) p = ⋁[ 𝒪 X ]-least (I V₁ , α V₁) (h V₂ , †)
   where
    p′ : (V₁ ⊆ₛ V₂) holds
    p′ = ⊆ₖ-implies-⊆ₛ V₁ V₂ p

    † : (h V₂ is-an-upper-bound-of (I V₁ , α V₁)) holds
    † (inl μ) = U        ≤⟨ ⋁[ 𝒪 X ]-upper _ (inl (p′ ⊤ₛ μ)) ⟩ h V₂ ■
    † (inr μ) = 𝟏[ 𝒪 X ] ≤⟨ ⋁[ 𝒪 X ]-upper _ (inr (p′ ⊥ₛ μ)) ⟩ h V₂ ■

\end{code}

We now prove that it preserves the top element and the binary meets.

\begin{code}

  φ : h 𝟏[ 𝒪 𝕊 ] ＝ 𝟏[ 𝒪 X ]
  φ = only-𝟏-is-above-𝟏 (𝒪 X) (h 𝟏[ 𝒪 𝕊 ]) γ
   where
    γ : (𝟏[ 𝒪 X ] ≤ h 𝟏[ 𝒪 𝕊 ]) holds
    γ = ⋁[ 𝒪 X ]-upper ((I 𝟏[ 𝒪 𝕊 ]) , (α 𝟏[ 𝒪 𝕊 ])) (inr ⋆)

  ψ : preserves-binary-meets (𝒪 𝕊) (𝒪 X) h holds
  ψ 𝔙 𝔚 = ≤-is-antisymmetric (poset-of (𝒪 X)) ψ₁ ψ₂
   where
    ψ₁ : (h (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) ≤ (h 𝔙 ∧[ 𝒪 X ] h 𝔚)) holds
    ψ₁ = ∧[ 𝒪 X ]-greatest
          (h 𝔙)
          (h 𝔚)
          (h (𝔙 ∧[ 𝒪 𝕊 ] 𝔚))
          (𝓂 ((𝔙 ∧[ 𝒪 𝕊 ] 𝔚) , _) (∧[ 𝒪 𝕊 ]-lower₁ 𝔙 𝔚))
          ((𝓂 ((𝔙 ∧[ 𝒪 𝕊 ] 𝔚) , 𝔚) (∧[ 𝒪 𝕊 ]-lower₂ 𝔙 𝔚)))

    υ : (h (𝔙 ∧[ 𝒪 𝕊 ] 𝔚)
          is-an-upper-bound-of
         ⁅ α 𝔙 i₁ ∧[ 𝒪 X ] α 𝔚 i₂ ∣ (i₁ , i₂) ∶ I 𝔙 × I 𝔚 ⁆) holds
    υ (inl p₁ , inl p₂) =
     α 𝔙 (inl p₁) ∧[ 𝒪 X ] α 𝔚 (inl p₂)                     ＝⟨ refl ⟩ₚ
     U ∧[ 𝒪 X ] U                                           ＝⟨ Ⅰ   ⟩ₚ
     U                                                      ≤⟨ Ⅱ  ⟩
     ⋁[ 𝒪 X ] ⁅ α (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) i ∣ i ∶ I (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) ⁆ ■
      where
       p : (⊤ₛ ∈ₛ (𝔙 ∧[ 𝒪 𝕊 ] 𝔚)) holds
       p = p₁ , p₂

       Ⅰ = ∧[ 𝒪 X ]-is-idempotent U ⁻¹
       Ⅱ = ⋁[ 𝒪 X ]-upper ⁅ α (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) i ∣ i ∶ I (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) ⁆ (inl p)
    υ (inl q₁ , inr p₂) =
     α 𝔙 (inl q₁) ∧[ 𝒪 X ] α 𝔚 (inr p₂)                     ＝⟨ refl ⟩ₚ
     U ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]                                    ＝⟨ Ⅰ   ⟩ₚ
     U                                                      ≤⟨ Ⅱ  ⟩
     ⋁[ 𝒪 X ] ⁅ α (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) i ∣ i ∶ I (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) ⁆ ■
      where
       p : (⊤ₛ ∈ₛ (𝔙 ∧[ 𝒪 𝕊 ] 𝔚)) holds
       p = q₁ , contains-⊥ₛ-implies-contains-⊤ₛ 𝔚 p₂

       Ⅰ = 𝟏-right-unit-of-∧ (𝒪 X) U
       Ⅱ = ⋁[ 𝒪 X ]-upper ⁅ α (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) i ∣ i ∶ I (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) ⁆ (inl p)
    υ (inr q₁ , inl p₂) =
     α 𝔙 (inr q₁) ∧[ 𝒪 X ] α 𝔚 (inl p₂)                     ＝⟨ refl ⟩ₚ
     𝟏[ 𝒪 X ] ∧[ 𝒪 X ] U                                    ＝⟨ Ⅰ   ⟩ₚ
     U                                                      ≤⟨ Ⅱ  ⟩
     ⋁[ 𝒪 X ] ⁅ α (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) i ∣ i ∶ I (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) ⁆ ■
      where
       p : (⊤ₛ ∈ₛ (𝔙 ∧[ 𝒪 𝕊 ] 𝔚)) holds
       p = contains-⊥ₛ-implies-contains-⊤ₛ 𝔙 q₁ , p₂

       Ⅰ = 𝟏-left-unit-of-∧ (𝒪 X) U
       Ⅱ = ⋁[ 𝒪 X ]-upper ⁅ α (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) i ∣ i ∶ I (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) ⁆ (inl p)
    υ (inr q₁ , inr q₂) =
     α 𝔙 (inr q₁) ∧[ 𝒪 X ] α 𝔚 (inr q₂)                      ＝⟨ refl ⟩ₚ
     𝟏[ 𝒪 X ] ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]                              ＝⟨ Ⅰ    ⟩ₚ
     𝟏[ 𝒪 X ]                                                ≤⟨  Ⅱ ⟩
     ⋁[ 𝒪 X ] ⁅ α (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) i ∣ i ∶ I (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) ⁆  ■
      where
       q : (⊥ₛ ∈ₛ (𝔙 ∧[ 𝒪 𝕊 ] 𝔚)) holds
       q = q₁ , q₂

       Ⅰ = ∧[ 𝒪 X ]-is-idempotent 𝟏[ 𝒪 X ] ⁻¹
       Ⅱ = ⋁[ 𝒪 X ]-upper ⁅ α (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) i ∣ i ∶ I (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) ⁆ (inr q)

    ψ₂ : ((h 𝔙 ∧[ 𝒪 X ] h 𝔚) ≤ h (𝔙 ∧[ 𝒪 𝕊 ] 𝔚)) holds
    ψ₂ =
     h 𝔙 ∧[ 𝒪 X ] h 𝔚                                             ＝⟨ refl ⟩ₚ
     h 𝔙 ∧[ 𝒪 X ] (⋁[ 𝒪 X ] ℱₓ 𝔚)                                 ＝⟨ Ⅱ ⟩ₚ
     ⋁[ 𝒪 X ] ⁅ α 𝔙 i₁ ∧[ 𝒪 X ] α 𝔚 i₂ ∣ (i₁ , i₂) ∶ I 𝔙 × I 𝔚 ⁆  ≤⟨ Ⅲ ⟩
     ⋁[ 𝒪 X ] ⁅ α (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) i ∣ i ∶ I (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) ⁆       ＝⟨ refl ⟩ₚ
     h (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) ■
      where
       Ⅱ = distributivity+ (𝒪 X) (I 𝔙 , α 𝔙) (I 𝔚  , α 𝔚)
       Ⅲ = ⋁[ 𝒪 X ]-least _ (_ , υ)

\end{code}

The fact that it satisfies the property `h truth ＝ U` is quite easy to see.

\begin{code}

  †₁ : (U ≤ h truth) holds
  †₁ = U ≤⟨ ⋁[ 𝒪 X ]-upper _ (inl ⋆) ⟩ h truth ■

  †₂ : (h truth ≤ U) holds
  †₂ = ⋁[ 𝒪 X ]-least (ℱₓ truth) (U , γ)
   where
    γ : (U is-an-upper-bound-of (ℱₓ truth)) holds
    γ (inl ⋆) = ≤-is-reflexive (poset-of (𝒪 X)) U

  † : U ＝ h truth
  † = ≤-is-antisymmetric (poset-of (𝒪 X)) †₁ †₂

\end{code}

We now proceed to prove that it preserves the joins.

\begin{code}

  open ScottLocaleProperties 𝕊𝓓 𝕊𝓓-has-least hscb pe

  ϑ : (𝔖 : Fam 𝓤 ⟨ 𝒪 𝕊 ⟩) → (h (⋁[ 𝒪 𝕊 ] 𝔖) is-lub-of ⁅ h 𝔘 ∣ 𝔘 ε 𝔖 ⁆) holds
  ϑ 𝔖 = ϑ₁ , λ { (V , υ) → ϑ₂ V υ }
   where
    ϑ₁ : (h (⋁[ 𝒪 𝕊 ] 𝔖) is-an-upper-bound-of ⁅ h 𝔘 ∣ 𝔘 ε 𝔖 ⁆) holds
    ϑ₁ i = 𝓂 (𝔖 [ i ] , ⋁[ 𝒪 𝕊 ] 𝔖) (⋁[ 𝒪 𝕊 ]-upper 𝔖 i)

    ϑ₂ : (W : ⟨ 𝒪 X ⟩)
       → (W is-an-upper-bound-of ⁅ h 𝔘 ∣ 𝔘 ε 𝔖 ⁆) holds
       → (h (⋁[ 𝒪 𝕊 ] 𝔖) ≤ W) holds
    ϑ₂ W υ = ⋁[ 𝒪 X ]-least (ℱₓ (⋁[ 𝒪 𝕊 ] 𝔖)) (W , γ)
     where
      γ : (W is-an-upper-bound-of (ℱₓ (⋁[ 𝒪 𝕊 ] 𝔖))) holds
      γ (inl μ) = ∥∥-rec (holds-is-prop (_ ≤ _)) ♣ μ
       where
        ♣ : (Σ k ꞉ index 𝔖 , (⊤ₛ ∈ₛ (𝔖 [ k ])) holds) → (U ≤ W) holds
        ♣ (k , μₖ) = U           ＝⟨ Ⅰ ⟩ₚ
                     h truth     ≤⟨ Ⅱ ⟩
                     h (𝔖 [ k ]) ≤⟨ Ⅲ ⟩
                     W           ■
                      where
                       Ⅰ = †
                       Ⅱ = 𝓂 _ (contains-⊤ₛ-implies-above-truth (𝔖 [ k ]) μₖ)
                       Ⅲ = υ k
      γ (inr μ) = ∥∥-rec (holds-is-prop (_ ≤ _)) ♥ μ
       where
        ♥ : (Σ k ꞉ index 𝔖 , (⊥ₛ ∈ₛ (𝔖 [ k ])) holds) → (𝟏[ 𝒪 X ] ≤ W) holds
        ♥ (k , μₖ) =
         𝟏[ 𝒪 X ]    ＝⟨ Ⅰ ⟩ₚ
         h 𝟏[ 𝒪 𝕊 ]  ＝⟨ Ⅱ ⟩ₚ
         h (𝔖 [ k ]) ≤⟨ Ⅲ  ⟩
         W           ■
          where
           Ⅰ = φ ⁻¹
           Ⅱ = ap h (contains-bottom-implies-is-𝟏 (𝔖 [ k ]) μₖ) ⁻¹
           Ⅲ = υ k

\end{code}

We package these up into a continuous map of locales (recal that `X ─c→ Y`
denotes the type of continuous maps from locale `X` to locale `Y`).

\begin{code}

  𝒽 : X ─c→ 𝕊
  𝒽 = h , φ , ψ , ϑ

\end{code}

Finally, we show that `𝒽` is determined uniquely by this property.

\begin{code}

  ‡ : is-central (Σ (f , _) ꞉ (𝒪 𝕊 ─f→ 𝒪 X) , U ＝ f truth) (𝒽 , †)
  ‡ (ℊ@(g , φ₀ , ψ₀ , ϑ₀) , †₀) =
   to-subtype-＝
    (λ h → carrier-of-[ poset-of (𝒪 X) ]-is-set)
    (to-frame-homomorphism-＝ (𝒪 𝕊) (𝒪 X) 𝒽 ℊ γ)
     where
      𝓂′ : is-monotonic (poset-of (𝒪 𝕊)) (poset-of (𝒪 X)) g holds
      𝓂′ = frame-morphisms-are-monotonic (𝒪 𝕊) (𝒪 X) g (φ₀ , ψ₀ , ϑ₀)

      γ₁ : (𝔙 : ⟨ 𝒪 𝕊 ⟩) → (h 𝔙 ≤ g 𝔙) holds
      γ₁ 𝔙 = ⋁[ 𝒪 X ]-least (ℱₓ 𝔙) (g 𝔙 , β₁)
       where
        β₁ : (g 𝔙 is-an-upper-bound-of ℱₓ 𝔙) holds
        β₁ (inl p) = U ＝⟨ †₀ ⟩ₚ g truth ≤⟨ Ⅱ ⟩ g 𝔙 ■
                      where
                       Ⅱ = 𝓂′ (truth , 𝔙) (contains-⊤ₛ-implies-above-truth 𝔙 p)
        β₁ (inr p) = 𝟏[ 𝒪 X ] ＝⟨ Ⅰ ⟩ₚ g 𝟏[ 𝒪 𝕊 ] ＝⟨ Ⅱ ⟩ₚ g 𝔙 ■
                      where
                       Ⅰ = φ₀ ⁻¹
                       Ⅱ = ap g (contains-bottom-implies-is-𝟏 𝔙 p ⁻¹)

      γ₂ : (𝔙 : ⟨ 𝒪 𝕊 ⟩) → (g 𝔙 ≤ h 𝔙) holds
      γ₂ 𝔙 = g 𝔙                      ＝⟨ ap g cov ⟩ₚ
             g (⋁[ 𝒪 𝕊 ] 𝔖)           ＝⟨ ※ ⟩ₚ
             ⋁[ 𝒪 X ] ⁅ g 𝔅 ∣ 𝔅 ε 𝔖 ⁆ ≤⟨ ♢ ⟩
             h 𝔙                      ■
       where
        open Joins _⊆ₛ_
         renaming (_is-an-upper-bound-of_ to _is-an-upper-bound-ofₛ_)

        𝔖 = covering-familyₛ 𝕊 𝕊-is-spectralᴰ 𝔙

        ※ = ⋁[ 𝒪 X ]-unique ⁅ g 𝔅 ∣ 𝔅 ε 𝔖 ⁆ (g (⋁[ 𝒪 𝕊 ] 𝔖)) (ϑ₀ 𝔖)

        cov : 𝔙 ＝ ⋁[ 𝒪 𝕊 ] 𝔖
        cov = ⋁[ 𝒪 𝕊 ]-unique 𝔖 𝔙 (basisₛ-covers-do-cover 𝕊 𝕊-is-spectralᴰ 𝔙)

        cov₀ : (𝔙 is-an-upper-bound-ofₛ 𝔖) holds
        cov₀ bs = ⊆ₖ-implies-⊆ₛ
                   (𝔖 [ bs ])
                   𝔙
                   (pr₁ (basisₛ-covers-do-cover 𝕊 𝕊-is-spectralᴰ 𝔙) bs)

        final : (i : index 𝔖) → (g (𝔖 [ i ]) ≤ h 𝔙) holds
        final (bs , b) = cases₃ case₁ case₂ case₃ (basis-trichotomy bs)
         where
          open PosetReasoning poset-of-scott-opensₛ
           renaming (_≤⟨_⟩_ to _≤⟨_⟩ₛ_;
                     _■ to _■ₛ;
                     _＝⟨_⟩ₚ_ to _＝⟨_⟩ₛ_)

          case₁ : ℬ𝕊 [ bs ] ＝ 𝟏[ 𝒪 𝕊 ]
                → (g (𝔖 [ bs , b ]) ≤ h 𝔙) holds
          case₁ q = transport (λ - → (g (𝔖 [ bs , b ]) ≤ h -) holds)
                     r
                     (g (ℬ𝕊 [ bs ]) ≤⟨ 𝟏-is-top (𝒪 X) (g (ℬ𝕊 [ bs ])) ⟩
                     𝟏[ 𝒪 X ]       ＝⟨ φ ⁻¹ ⟩ₚ h 𝟏[ 𝒪 𝕊 ] ■)
           where
            χ : (𝟏[ 𝒪 𝕊 ] ⊆ₛ (ℬ𝕊 [ bs ])) holds
            χ = reflexivity+ poset-of-scott-opensₛ (q ⁻¹)

            r : 𝟏[ 𝒪 𝕊 ] ＝ 𝔙
            r = ⊆ₛ-is-antisymmetric
                 (λ x p → cov₀ (bs , b) x (χ x p))
                 (⊤ₛ-is-top 𝔙)

          case₂ : ℬ𝕊 [ bs ] ＝ truth
                → (g (𝔖 [ bs , b ]) ≤ h 𝔙) holds
          case₂ p = g (𝔖 [ bs , b ]) ＝⟨ refl ⟩ₚ
                    g (ℬ𝕊 [ bs ])    ＝⟨ Ⅰ ⟩ₚ
                    g truth          ＝⟨ Ⅱ ⟩ₚ
                    U                ≤⟨  Ⅲ ⟩
                    h 𝔙              ■
           where
            p₀ : (truth ⊆ₛ (ℬ𝕊 [ bs ])) holds
            p₀ = reflexivity+ poset-of-scott-opensₛ (p ⁻¹)

            ζ : (truth ⊆ₛ 𝔙) holds
            ζ P μ = cov₀ (bs , b) P (p₀ P μ)

            χ : (⊤ₛ ∈ₛ 𝔙) holds
            χ = above-truth-implies-contains-⊤ₛ 𝔙 (⊆ₛ-implies-⊆ₖ truth 𝔙 ζ)

            Ⅰ = ap g p
            Ⅱ = †₀ ⁻¹
            Ⅲ = ⋁[ 𝒪 X ]-upper (ℱₓ 𝔙) (inl χ)

          case₃ : ℬ𝕊 [ bs ] ＝ 𝟎[ 𝒪 𝕊 ] → (g (𝔖 [ bs , b ]) ≤ h 𝔙) holds
          case₃ q = g (𝔖 [ bs , b ]) ＝⟨ refl   ⟩ₚ
                    g (ℬ𝕊 [ bs ])    ＝⟨ Ⅰ ⟩ₚ
                    g 𝟎[ 𝒪 𝕊 ]       ＝⟨ Ⅱ ⟩ₚ
                    𝟎[ 𝒪 X ]         ≤⟨ Ⅲ ⟩
                    h 𝔙              ■
                     where
                      Ⅰ = ap g q
                      Ⅱ = frame-homomorphisms-preserve-bottom (𝒪 𝕊) (𝒪 X) ℊ
                      Ⅲ = 𝟎-is-bottom (𝒪 X) (h 𝔙)

        ♢ : ((⋁[ 𝒪 X ] ⁅ g 𝔅 ∣ 𝔅 ε 𝔖 ⁆) ≤ h 𝔙) holds
        ♢ = ⋁[ 𝒪 X ]-least ⁅ g 𝔅 ∣ 𝔅 ε 𝔖 ⁆ (h 𝔙 , final)

      γ : (𝔙 : ⟨ 𝒪 𝕊 ⟩) → h 𝔙 ＝ g 𝔙
      γ 𝔙 = ≤-is-antisymmetric (poset-of (𝒪 X)) (γ₁ 𝔙) (γ₂ 𝔙)

\end{code}
