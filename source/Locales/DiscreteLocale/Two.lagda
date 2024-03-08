--------------------------------------------------------------------------------
title:          Two
author:         Ayberk Tosun
date-started:   2024-03-04
date-completed: 2024-03-04
--------------------------------------------------------------------------------

We define the locale corresponding to the two-point discrete space.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons

module Locales.DiscreteLocale.Two
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DiscreteLocale.Definition fe pe pt
open import Locales.Frame pt fe
open import MLTT.Spartan hiding (𝟚)
open import Slice.Family
open import UF.Logic
open import UF.Sets
open import UF.DiscreteAndSeparated hiding (𝟚-is-set)
open import UF.Powerset
open import UF.SubtypeClassifier

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)
open PropositionalSubsetInclusionNotation fe
open PropositionalTruncation pt hiding (_∨_)

\end{code}

\begin{code}

module _ (𝓤 : Universe) where

 𝟚-is-set : {𝓤 : Universe} → is-set (𝟚 𝓤)
 𝟚-is-set {𝓤} = +-is-set (𝟙 {𝓤}) (𝟙 {𝓤}) 𝟙-is-set 𝟙-is-set

 𝟚-loc : Locale (𝓤 ⁺) 𝓤 𝓤
 𝟚-loc = discrete-locale (𝟚 𝓤) 𝟚-is-set

\end{code}
