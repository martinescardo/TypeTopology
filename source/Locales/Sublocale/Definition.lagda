---
title:  Definition of sublocale
author: Ayberk Tosun
date:   2026-10-31
---

In this module, we define the notion of sublocale using nuclei.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc

module Locales.Sublocale.Definition
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.ContinuousMap.Homeomorphism-Definition pt fe
open import Locales.Frame pt fe
open import Locales.Sublocale.Nucleus pt fe
open import Locales.Sublocale.SublocaleDeterminedByNucleus pt fe
open import MLTT.Spartan
open import UF.Logic
open import UF.SubtypeClassifier

open AllCombinators pt fe
open Locale

\end{code}

A sublocale of a locale `X` is one that is determined by a nucleus on `X`. In
other words, a locale `Y` is a sublocale of `X` if there is a nucleus
`j : 𝒪 X → 𝒪 X` such that `X_j` is homeomorphic to `Y`.

\begin{code}

exhibits-as-a-sublocale-of
 : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
 → (𝒿 : Nucleus (𝒪 X))
 → Locale (𝓤 ⁺) 𝓤 𝓤
 → 𝓤 ⁺  ̇
exhibits-as-a-sublocale-of X 𝒿 Y = Y ≅c≅ Xⱼ
 where
  open Sublocale-Determined-By-Nucleus

  Xⱼ = sublocale-determined-by-nucleus X 𝒿

_is-sublocale-of_ : (Y X : Locale (𝓤 ⁺) 𝓤 𝓤) → Ω (𝓤 ⁺)
Y is-sublocale-of X = Ǝ 𝒿 ꞉ Nucleus (𝒪 X) , exhibits-as-a-sublocale-of X 𝒿 Y

\end{code}
