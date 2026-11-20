---
title: Downward-closed sets
author: Ayberk Tosun
date: 2026-11-20
---

The notion of down set was used in many places throughout the locale theory
development. In this module, we define it in its most general form to avoid
duplication. We also collect lemmas about it here.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc

module Locales.DownSet
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.Frame pt fe hiding (⟨_⟩)
open import MLTT.Spartan
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.SubtypeClassifier

open AllCombinators pt fe

\end{code}

We define what it means for a subset `U` to downward closed with respect to
some order `_≤_`. We do not assume anything about the order.

\begin{code}

is-downward-closed : {A : 𝓤  ̇} → (_≤_ : A → A → Ω 𝓥) → 𝓟 {𝓦} A → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
is-downward-closed {_} {_} {_} {A} _≤_ U =
 Ɐ u ꞉ A , u ∈ₚ U ⇒ (Ɐ a ꞉ A , a ≤ u ⇒ a ∈ₚ U)

\end{code}
