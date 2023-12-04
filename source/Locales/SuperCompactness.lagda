---
author:       Ayberk Tosun
date-started: 2023-12-04
---

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt

module Locales.SuperCompactness (pt : propositional-truncations-exist)
                                (fe : Fun-Ext)                             where

open import MLTT.Spartan
open import UF.SubtypeClassifier
open import Locales.Frame pt fe
open import Locales.WayBelowRelation.Definition  pt fe
open import Slice.Family
open import UF.Logic

open PropositionalTruncation pt
open AllCombinators pt fe
open Locale

\end{code}

An open `U : 𝒪(X)` of a locale `X` is called super-compact if.

\begin{code}

is-super-compact-open : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-super-compact-open {_} {_} {𝓦} X U =
 Ɐ S ꞉ Fam 𝓦 ⟨ 𝒪 X ⟩ ,
  U ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] S) ⇒
   (Ǝ i ꞉ index S , (U ≤[ poset-of (𝒪 X) ] S [ i ]) holds)

\end{code}
