---
title:          Equivalence of sharp elements with spectral points
author:         Ayberk Tosun
date-started:   2024-05-26
---

The formalization of a proof.

\begin{code}

{--# OPTIONS --safe --without-K #--}

open import MLTT.List hiding ([_])
open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

module Locales.Point.SpectralPoint-Definition
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Locales.Frame pt fe
open import Locales.ContinuousMap.Definition pt fe
open import Locales.InitialFrame pt fe
open import UF.SubtypeClassifier

\end{code}

\begin{code}

module Notion-Of-Spectral-Point (X : Locale (𝓤 ⁺) 𝓤 𝓤) where

 open ContinuousMaps X (𝟏Loc pe)
 open Locale

\end{code}

\begin{code}

 record Spectral-Point : {!!}  ̇ where
  field
   point : ⟨ 𝒪 X ⟩ → Ω 𝓤

   point-preserves-top : {!!}

\end{code}
