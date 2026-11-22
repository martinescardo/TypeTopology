---
title:  Downward-closed sets
author: Ayberk Tosun
date:   2026-11-20
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
open import UF.Powerset
open import UF.SubtypeClassifier

open AllCombinators pt fe

\end{code}

We define what it means for a subset `U` to downward closed with respect to
some order `_≤_`. We do not assume anything about the order.

\begin{code}

is-downward-closed : {A : 𝓤  ̇} → (_≤_ : A → A → Ω 𝓥) → 𝓟' {𝓦} A → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
is-downward-closed {_} {_} {_} {A} _≤_ U =
 Ɐ u ꞉ A , u ∈ₚ U ⇒ (Ɐ a ꞉ A , a ≤ u ⇒ a ∈ₚ U)

\end{code}

By `Downward-Closed-Subset' 𝓦` we denote the type of `𝓦`-valued downward-closed
subsets.

\begin{code}

Downward-Closed-Subset' : (𝓦 : Universe)
                        → {A : 𝓤  ̇}
                        → (_≤_ : A → A → Ω 𝓥)
                        → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
Downward-Closed-Subset' {_} {_} 𝓦 {A} _≤_ =
 Σ U ꞉ 𝓟' {𝓦} A , is-downward-closed _≤_ U holds

\end{code}

In most cases, we work with down sets in the same as universe as that of the
type in consideration. We define a special case for this. Our use of the prime
symbol here follows the convention of `𝓟` and `𝓟'` from the `UF.Powerset`
module.

\begin{code}

Downward-Closed-Subset : {A : 𝓤  ̇} → (_≤_ : A → A → Ω 𝓥) → 𝓤 ⁺ ⊔ 𝓥  ̇
Downward-Closed-Subset {𝓤} {_} {A} _≤_ = Downward-Closed-Subset' 𝓤 _≤_

\end{code}

We also give a direct definition of the downward-closed subsets of a poset,
which we denoted by `Downward-Closed-Subsetₚ`.

\begin{code}

Downward-Closed-Subsetₚ : (P : Poset 𝓤 𝓥) → 𝓤 ⁺ ⊔ 𝓥  ̇
Downward-Closed-Subsetₚ P = Downward-Closed-Subset (λ x y → x ≤[ P ] y)

\end{code}
