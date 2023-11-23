---
title:       Properties of the Scott locale
author:      Ayberk Tosun
start-date:  2023-11-23
---

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.List hiding ([_])
open import MLTT.Pi
open import MLTT.Spartan
open import Slice.Family
open import UF.Base
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.Univalence

\end{code}

We assume the existence of propositional truncations as well as function
extensionality.

\begin{code}

module Locales.ScottLocale.Properties (pt : propositional-truncations-exist)
                                      (fe : Fun-Ext)
                                      (𝓤  : Universe)
                                      where

open import Locales.Frame                                    pt fe
open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤
open import Locales.ScottLocale.Definition                   pt fe 𝓤

open Locale

open import DomainTheory.Basics.Dcpo                         pt fe 𝓤
 renaming (⟨_⟩ to ⟨_⟩∙)
 hiding   (is-directed)
open import DomainTheory.Basics.Pointed                      pt fe 𝓤
 renaming (⊥ to ⊥d)
open import DomainTheory.Topology.ScottTopology        pt fe 𝓤
open import DomainTheory.Topology.ScottTopologyProperties pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Bases      pt fe 𝓤
open import DomainTheory.Basics.WayBelow               pt fe 𝓤

\end{code}

\begin{code}

module ScottLocaleProperties (𝓓 : DCPO {𝓤 ⁺} {𝓤})
                             (hl : has-least (underlying-order 𝓓))
                             (hscb : has-specified-small-compact-basis 𝓓)
                             (pe   : propext 𝓤)                            where

 open ScottLocaleConstruction 𝓓 hscb pe

 open Properties  𝓓
 open BottomLemma 𝓓 𝕒 hl

 ⊥κ : is-compact 𝓓 ⊥ᴰ
 ⊥κ = ⊥-is-compact (𝓓 , hl)

 Σ⦅𝓓⦆ : Locale (𝓤 ⁺) 𝓤 𝓤
 Σ⦅𝓓⦆ = ScottLocale

 open DefnOfScottLocale 𝓓 𝓤 pe using (_⊆ₛ_)

 ↑⊥-is-below-𝟏 : (𝟏[ 𝒪 Σ⦅𝓓⦆ ] ⊆ₛ ↑ˢ[ ⊥ᴰ , ⊥κ ]) holds
 ↑⊥-is-below-𝟏 = bottom-principal-filter-is-top 𝟏[ 𝒪 Σ⦅𝓓⦆ ]

 ↑⊥-is-top : ↑ˢ[ ⊥ᴰ , ⊥κ ] ＝ 𝟏[ 𝒪 Σ⦅𝓓⦆ ]
 ↑⊥-is-top = only-𝟏-is-above-𝟏 (𝒪 Σ⦅𝓓⦆) ↑ˢ[ ⊥ᴰ , ⊥κ ] †
  where
   † : (𝟏[ 𝒪 Σ⦅𝓓⦆ ] ≤[ poset-of (𝒪 Σ⦅𝓓⦆) ] ↑ˢ[ ⊥ᴰ , ⊥κ ]) holds
   † = ⊆ₛ-implies-⊆ₖ 𝟏[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ ⊥ᴰ , ⊥κ ] ↑⊥-is-below-𝟏

\end{code}
