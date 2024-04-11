--------------------------------------------------------------------------------
title:          Homeomorphisms of locales
author:         Ayberk Tosun
date-started:   2024-04-11
--------------------------------------------------------------------------------

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.List hiding ([_])
open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc

module Locales.ContinuousMap.Homeomorphism-Definition
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.ContinuousMap.Definition pt fe
open import Locales.Frame pt fe
open import Slice.Family
open import UF.Equiv
open import UF.Hedberg
open import UF.Logic
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open AllCombinators pt fe

\end{code}

A homeomorphism between locales `X` and `Y` is an isomorphism between their
defining frames.

\begin{code}

Homeomorphism : (X : Locale 𝓤  𝓥  𝓦)
              → (Y : Locale 𝓤' 𝓥' 𝓦)
              → {!!}
Homeomorphism X Y = {!!}

\end{code}
