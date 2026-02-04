---
title:         Properties of the Scott locale
author:        Ayberk Tosun
date-started:  2023-11-23
dates-updated: [2024-03-16]
---

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import Slice.Family
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.Subsingletons

\end{code}

We assume the existence of propositional truncations as well as function
extensionality.

\begin{code}

module Locales.ScottLocale.Properties (pt : propositional-truncations-exist)
                                      (fe : Fun-Ext)
                                      (𝓤  : Universe) where

open import DomainTheory.BasesAndContinuity.Bases            pt fe 𝓤
open import DomainTheory.Basics.Dcpo                         pt fe 𝓤
 renaming (⟨_⟩ to ⟨_⟩∙) hiding   (is-directed)
open import DomainTheory.Basics.WayBelow                     pt fe 𝓤
open import DomainTheory.Topology.ScottTopology              pt fe 𝓤
open import DomainTheory.Topology.ScottTopologyProperties    pt fe 𝓤
open import Locales.Compactness.Definition                              pt fe
 hiding (is-compact)
open import Locales.Frame                                    pt fe
open import Locales.ScottLocale.Definition                   pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤

open AllCombinators pt fe
open Locale
open PropositionalTruncation pt

\end{code}

Moved from the `ScottLocalesOfScottDomains` module to here on 2024-03-16.

\begin{code}

bounded-above : (𝓓 : DCPO {𝓤 ⁺} {𝓤}) → ⟨ 𝓓 ⟩∙ → ⟨ 𝓓 ⟩∙ → Ω (𝓤 ⁺)
bounded-above 𝓓 x y = ∥ upper-bound (binary-family 𝓤 x y) ∥Ω
 where
  open Joins (λ a b → a ⊑⟨ 𝓓 ⟩ₚ b)

infix 30 bounded-above

syntax bounded-above 𝓓 x y = x ↑[ 𝓓 ] y

\end{code}

\begin{code}

module ScottLocaleProperties
        (𝓓    : DCPO {𝓤 ⁺} {𝓤})
        (hl   : has-least (underlying-order 𝓓))
        (hscb : has-specified-small-compact-basis 𝓓)
        (pe   : propext 𝓤)
       where

 open ScottLocaleConstruction 𝓓 hscb pe

 private
  B : 𝓤 ̇
  B = index-of-compact-basis 𝓓 hscb

  β : B → ⟨ 𝓓 ⟩∙
  β i = family-of-compact-elements 𝓓 hscb i

 open Properties  𝓓
 open BottomLemma 𝓓 𝕒 hl

 ⊥κ : is-compact 𝓓 ⊥ᴰ
 ⊥κ = ⊥-is-compact (𝓓 , hl)

 Σ⦅𝓓⦆ : Locale (𝓤 ⁺) 𝓤 𝓤
 Σ⦅𝓓⦆ = ScottLocale

 open DefnOfScottLocale 𝓓 𝓤 pe using (_⊆ₛ_)

\end{code}

Recall that `↑ˢ[ x , p ]` denotes the principal filter on a compact element `x`,
(where `p` is the proof that `x` is compact).

Below, we prove that `↑ˢ[ ⊥ᵈ , p ] = 𝟏` where `𝟏` is the top Scott open of the
Scott locale on `𝓓`.

\begin{code}

 ↑⊥-is-below-𝟏 : (𝟏[ 𝒪 Σ⦅𝓓⦆ ] ⊆ₛ ↑ˢ[ ⊥ᴰ , ⊥κ ]) holds
 ↑⊥-is-below-𝟏 = bottom-principal-filter-is-top 𝟏[ 𝒪 Σ⦅𝓓⦆ ]

 ↑⊥-is-top : ↑ˢ[ ⊥ᴰ , ⊥κ ] ＝ 𝟏[ 𝒪 Σ⦅𝓓⦆ ]
 ↑⊥-is-top = only-𝟏-is-above-𝟏 (𝒪 Σ⦅𝓓⦆) ↑ˢ[ ⊥ᴰ , ⊥κ ] †
  where
   † : (𝟏[ 𝒪 Σ⦅𝓓⦆ ] ≤[ poset-of (𝒪 Σ⦅𝓓⦆) ] ↑ˢ[ ⊥ᴰ , ⊥κ ]) holds
   † = ⊆ₛ-implies-⊆ₖ 𝟏[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ ⊥ᴰ , ⊥κ ] ↑⊥-is-below-𝟏

 open DefnOfScottTopology 𝓓 𝓤

 contains-bottom-implies-is-𝟏 : (𝔘 : ⟨ 𝒪 Σ⦅𝓓⦆ ⟩)
                              → (⊥ᴰ ∈ₛ 𝔘) holds
                              → 𝔘 ＝ 𝟏[ 𝒪 Σ⦅𝓓⦆ ]
 contains-bottom-implies-is-𝟏 𝔘 μ = only-𝟏-is-above-𝟏 (𝒪 Σ⦅𝓓⦆) 𝔘 †
  where
   † : (𝟏[ 𝒪 ScottLocale ] ⊆ₖ 𝔘) holds
   † = ⊆ₛ-implies-⊆ₖ
        𝟏[ 𝒪 ScottLocale ]
        𝔘
        (λ { x ⋆ → contains-bottom-implies-is-top 𝔘 μ x})

\end{code}

Moved from the `ScottLocalesOfScottDomains` module to here on 2024-03-16.

The principal filter `↑(x)` on any `x : 𝓓` is a compact Scott open.

\begin{code}

 principal-filter-is-compact₀ : (c : ⟨ 𝓓 ⟩∙)
                              → (κ : is-compact 𝓓 c)
                              → is-compact-open Σ⦅𝓓⦆ ↑ˢ[ (c , κ) ] holds
 principal-filter-is-compact₀ c κ S δ p = ∥∥-functor † μ
  where
   μ : (c ∈ₛ (⋁[ 𝒪 Σ⦅𝓓⦆ ] S)) holds
   μ = ⊆ₖ-implies-⊆ₛ ↑ˢ[ (c , κ) ] (⋁[ 𝒪 Σ⦅𝓓⦆ ] S) p c (reflexivity 𝓓 c)

   † : Σ i ꞉ index S , (c ∈ₛ (S [ i ])) holds
     → Σ i ꞉ index S , (↑ˢ[ (c , κ) ] ≤[ poset-of (𝒪 Σ⦅𝓓⦆) ] S [ i ]) holds
   † (i , r) = i , ‡
    where
     ‡ :  (↑ˢ[ c , κ ] ≤[ poset-of (𝒪 Σ⦅𝓓⦆) ] (S [ i ])) holds
     ‡ d = upward-closure (S [ i ]) c (β d) r

\end{code}

Moved from the `ScottLocalesOfScottDomains` module to here on 2024-03-16.

The Scott locale is always compact.

\begin{code}

 ⊤-is-compact : is-compact-open Σ⦅𝓓⦆ 𝟏[ 𝒪 Σ⦅𝓓⦆ ] holds
 ⊤-is-compact = transport (λ - → is-compact-open Σ⦅𝓓⦆ - holds) ↑⊥-is-top †
  where
   † : is-compact-open ScottLocale ↑ˢ[ ⊥ᴰ , ⊥κ ] holds
   † = principal-filter-is-compact₀ ⊥ᴰ ⊥κ

\end{code}

Moved from the `ScottLocalesOfScottDomains` module to here on 2024-03-16.

If two compact elements `c` and `d` do not have an upper bound, then the meet
of their principal filters is the empty Scott open.

\begin{code}

 not-bounded-lemma : (c d : ⟨ 𝓓 ⟩∙)
                   → (κᶜ : is-compact 𝓓 c)
                   → (κᵈ : is-compact 𝓓 d)
                   → ¬ ((c ↑[ 𝓓 ] d) holds)
                   → ↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ d , κᵈ ] ＝ 𝟎[ 𝒪 Σ⦅𝓓⦆ ]
 not-bounded-lemma c d κᶜ κᵈ ν =
  only-𝟎-is-below-𝟎 (𝒪 Σ⦅𝓓⦆) (↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ d , κᵈ ]) †
   where
    † : ((↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ d , κᵈ ]) ⊆ₖ 𝟎[ 𝒪 Σ⦅𝓓⦆ ]) holds
    † i (p₁ , p₂) = 𝟘-elim (ν ∣ β i , (λ { (inl ⋆) → p₁ ; (inr ⋆) → p₂}) ∣)

\end{code}
