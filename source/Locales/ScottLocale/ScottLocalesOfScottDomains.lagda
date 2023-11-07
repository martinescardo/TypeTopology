---
title:       The spectral Scott locale of a Scott domain
author:      Ayberk Tosun
start-date:  2023-10-25
---

Ayberk Tosun.

Started on: 2023-10-25.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.List
open import Slice.Family
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Powerset-MultiUniverse
open import UF.Size

module Locales.ScottLocale.ScottLocalesOfScottDomains
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
        (𝓤  : Universe) where

open import DomainTheory.Basics.Dcpo                         pt fe 𝓤
 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Basics.Pointed                      pt fe 𝓤
 renaming (⊥ to ⊥d)
open import DomainTheory.BasesAndContinuity.Bases            pt fe 𝓤
open import DomainTheory.BasesAndContinuity.CompactBasis     pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤
open import DomainTheory.Topology.ScottTopology              pt fe 𝓤
open import DomainTheory.Topology.ScottTopologyProperties    pt fe 𝓤
open import Locales.Frame                                    pt fe
 hiding (∅)

open import Locales.SmallBasis pt fe sr

open Universal fe
open Implication fe
open Existential pt
open Disjunction pt
open Conjunction
open PowersetOperations

open Locale

open PropositionalTruncation pt hiding (_∨_)

\end{code}

\begin{code}

module SpectralScottLocaleConstruction
        (𝓓    : DCPO {𝓤 ⁺} {𝓤})
        (hscb : has-specified-small-compact-basis 𝓓)
        (pe   : propext 𝓤) where

 open ScottLocaleConstruction 𝓓

\end{code}

We denote by `𝒮𝓓` the Scott locale of the dcpo `𝓓`.

\begin{code}

 𝒮𝓓 : Locale (𝓤 ⁺) 𝓤 𝓤
 𝒮𝓓 = ScottLocale hscb pe

\end{code}

We denote by `(B, β)` the algebraic basis of the pointed dcpo 𝓓.

\begin{code}

 B : 𝓤  ̇
 B = index-of-compact-basis 𝓓 hscb

 β : B → ⟨ 𝓓 ⟩∙
 β i = family-of-basic-opens 𝓓 hscb i

\end{code}

We define some nice notation for the prop-valued equality of the dcpo `𝓓`.

\begin{code}

 _＝ₚ_ : ⟨ 𝓓 ⟩∙ → ⟨ 𝓓 ⟩∙ → Ω (𝓤 ⁺)
 x ＝ₚ y = (x ＝ y) , sethood 𝓓

\end{code}

We now construct the basis for this locale.

\begin{code}

 from-list₀ : List B → 𝓟 {𝓤 ⁺} {𝓤 ⁺} ⟨ 𝓓 ⟩∙
 from-list₀ []       = ∅
 from-list₀ (b ∷ bs) = λ x → x ∈ₚ ↑[ 𝓓 ] (β b) ∨ x ∈ₚ from-list₀ bs

 from-list-is-upwards-closed : List B → {!is-upwards-closed!}
 from-list-is-upwards-closed = {!!}

 from-list : List B → ⟨ 𝒪 𝒮𝓓 ⟩
 from-list = {!!}

 basis-for-𝒮𝓓 : Fam 𝓤 ⟨ 𝒪 𝒮𝓓 ⟩
 basis-for-𝒮𝓓 = List B , from-list

 σᴰ : spectralᴰ 𝒮𝓓
 σᴰ = basis-for-𝒮𝓓 , {!!} , ({!!} , (τ , μ))
  where
   τ : contains-top (𝒪 𝒮𝓓) basis-for-𝒮𝓓 holds
   τ = {!!}

   μ : closed-under-binary-meets (𝒪 𝒮𝓓) basis-for-𝒮𝓓 holds
   μ = {!!}

\end{code}
