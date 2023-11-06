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
open import DomainTheory.BasesAndContinuity.Bases            pt fe 𝓤
open import DomainTheory.BasesAndContinuity.CompactBasis     pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤
open import Locales.Frame                                    pt fe

open import Locales.SmallBasis pt fe sr

open Universal fe
open Implication fe
open Existential pt
open Conjunction

open Locale

open PropositionalTruncation pt

\end{code}

\begin{code}

module SpectralScottLocaleConstruction
        (𝓓 : DCPO {𝓤 ⁺} {𝓤})
        (hscb : has-specified-small-compact-basis 𝓓)
        (pe : propext 𝓤) where

 open ScottLocaleConstruction 𝓓

\end{code}

We denote by `𝒮𝓓` the Scott locale of the dcpo `𝓓`.

\begin{code}

 𝒮𝓓 : Locale (𝓤 ⁺) 𝓤 𝓤
 𝒮𝓓 = ScottLocale hscb pe

 B𝓓 : 𝓤  ̇
 B𝓓 = index-of-compact-basis 𝓓 hscb

\end{code}

We now construct the basis for this locale.

\begin{code}

 from-list₀ : List B𝓓 → 𝓟 ⟨ 𝓓 ⟩∙
 from-list₀ []       = {!!}
 from-list₀ (k ∷ ks) = {!!}

 from-list : List B𝓓 → ⟨ 𝒪 𝒮𝓓 ⟩
 from-list = {!!}

 basis-for-𝒮𝓓 : Fam 𝓤 ⟨ 𝒪 𝒮𝓓 ⟩
 basis-for-𝒮𝓓 = List B𝓓 , from-list

 σᴰ : spectralᴰ 𝒮𝓓
 σᴰ = basis-for-𝒮𝓓 , {!!} , ({!!} , (τ , μ))
  where
   τ : contains-top (𝒪 𝒮𝓓) basis-for-𝒮𝓓 holds
   τ = {!!}

   μ : closed-under-binary-meets (𝒪 𝒮𝓓) basis-for-𝒮𝓓 holds
   μ = {!!}

\end{code}
