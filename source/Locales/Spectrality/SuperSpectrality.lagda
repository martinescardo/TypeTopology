---
title:        Superspectral Locales
date-started: 2023-12-04
author:       Ayberk Tosun
---

\begin{code}

open import UF.PropTrunc
open import UF.FunExt

module Locales.Spectrality.SuperSpectrality
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
         where

open import Locales.Compactness pt fe
open import Locales.Frame pt fe
open import MLTT.Spartan
open import UF.Logic
open import UF.SubtypeClassifier

open PropositionalTruncation pt
open AllCombinators pt fe
open Locale

\end{code}

\begin{code}

is-super-spectral : Locale 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-super-spectral {_} {_} {𝓦} X = {!!} -- ⦅𝟏⦆ ∧ ⦅𝟐⦆

\end{code}
