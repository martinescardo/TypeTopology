--------------------------------------------------------------------------------
title:          Properties of continuous maps
author:         Ayberk Tosun
date-started:   2024-04-10
--------------------------------------------------------------------------------

Factored out from the `Locales.Frame` module on 2024-04-10.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import MLTT.List hiding ([_])

module Locales.ContinuousMap.Properties
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.Frame pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
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

\begin{code}

\end{code}
