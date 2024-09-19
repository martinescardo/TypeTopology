---
title:          Frame homomorphisms
author:         Ayberk Tosun
date-started:   2024-09-19
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Size
open import UF.SubtypeClassifier

module Locales.ThesisIndex
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.Frame pt fe
open import OrderedTypes.SupLattice pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe

\end{code}

\section{Basics of pointfree topology}

\begin{code}

definition∶frame : (𝓤 𝓥 𝓦 : Universe) → (𝓤 ⊔ 𝓥 ⊔ 𝓦) ⁺  ̇
definition∶frame = Frame

lemma∶partial-order-gives-sethood : (X : 𝓤  ̇)
                                  → (_≤_ : X → X → Ω 𝓥)
                                  → is-partial-order X _≤_
                                  → is-set X
lemma∶partial-order-gives-sethood {𝓤} {𝓥} X _≤_ ϑ =
 carrier-of-[ P ]-is-set
  where
   P : Poset 𝓤 𝓥
   P = X , _≤_ , ϑ

\end{code}

\subsection{Primer on predicative lattice theory}

\begin{code}

sup-complete : (𝓤 𝓣 𝓥 : Universe) {A : 𝓤 ̇}
             → sup-lattice-data 𝓤 𝓣 𝓥 A → 𝓤 ⊔ 𝓣 ⊔ 𝓥 ⁺ ̇
sup-complete = is-sup-lattice

\end{code}

\subsection{Categories of frames and locales}

Given frames `K` and `L`, the type of frame homomorphisms from `K` into `L` is
denoted `K ─f→ L`.

\begin{code}

definition∶frame-homomorphism : Frame 𝓤 𝓥 𝓦 → Frame 𝓤' 𝓥' 𝓦 → 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓤' ⊔ 𝓥'  ̇
definition∶frame-homomorphism =
 FrameHomomorphisms._─f→_

\end{code}
