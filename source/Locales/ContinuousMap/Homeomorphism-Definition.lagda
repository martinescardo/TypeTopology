--------------------------------------------------------------------------------
title:          Homeomorphisms of locales
author:         Ayberk Tosun
date-started:   2024-04-11
date-completed: 2024-04-18
--------------------------------------------------------------------------------

A homeomorphism of locales is the same thing as an isomorphism of their
underlying frames. As we maintain a careful distinction between locales and
their defining frames, however, we give a different name to this notion.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc

module Locales.ContinuousMap.Homeomorphism-Definition
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameIsomorphism-Definition pt fe
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
open Locale

\end{code}

A homeomorphism between locales `X` and `Y` is an isomorphism between their
defining frames.

\begin{code}

Homeomorphism : Locale 𝓤  𝓥  𝓦 → Locale 𝓤' 𝓥' 𝓦 → 𝓤' ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓥' ⊔ 𝓦 ⁺  ̇
Homeomorphism X Y = Isomorphismᵣ (𝒪 Y) (𝒪 X)
 where
  open FrameIsomorphisms

\end{code}

Declare syntax for homeomorphisms.

\begin{code}

Homeomorphism-Syntax : Locale 𝓤 𝓥 𝓦 → Locale 𝓤' 𝓥' 𝓦 → 𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥' ⊔ 𝓦 ⁺  ̇
Homeomorphism-Syntax = Homeomorphism

infix 0 Homeomorphism-Syntax
syntax Homeomorphism-Syntax X Y = X ≅c≅ Y

\end{code}
