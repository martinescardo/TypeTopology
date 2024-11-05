---
title:          Thesis Index
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
open import UF.Subsingletons
open import UF.SubtypeClassifier

module Locales.ThesisIndex
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.Frame pt fe
open import Locales.InitialFrame pt fe
open import Locales.Nucleus pt fe
open import OrderedTypes.SupLattice pt fe hiding (⟨_⟩)

open Locale

\end{code}

\section{Definition of the notion of frame}

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

\subsection{Local smallness of frames}

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

\section{Basic examples of locales}

\subsection{The terminal locale}

\begin{code}

example∶terminal-locale : (pe : Prop-Ext) (𝓤 : Universe) → Locale (𝓤 ⁺) 𝓤 𝓤
example∶terminal-locale pe _ = 𝟏Loc pe

\end{code}

\section{Sublocales}

Definition of the notion of nucleus:

\begin{code}

definition∶nucleus : Frame 𝓤 𝓥 𝓦 → 𝓤 ⊔ 𝓥  ̇
definition∶nucleus = Nucleus

\end{code}

The closed nucleus:

\begin{code}

example∶closed-nucleus : (X : Locale 𝓤 𝓥 𝓦) (U : ⟨ 𝒪 X ⟩) → Nucleus (𝒪 X)
example∶closed-nucleus = closed-nucleus

\end{code}

\section{Compactness and the way-below relation}

\subsection{Compact opens}

\subsection{The way-below relation}

\section{Clopens and the well-inside relation}

\subsection{Clopens}

\subsection{The well-inside relation}

\section{Bases}

\subsection{Intensional vs. extensional bases}

\subsection{Weak vs. strong bases}

\subsection{Directification of bases}

\subsection{Examples}

\section{Important classes of locales}

\section{Adjoint Functor Theorem for frames}

\subsection{Construction of Heyting implications}
