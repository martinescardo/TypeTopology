\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.FunExt
open import UF.PropTrunc

module Locales.PatchJournalIndex (pt : propositional-truncations-exist)
                                 (fe : Fun-Ext)                          where

open import Locales.Frame pt fe
open import Locales.Nucleus pt fe
open import MGS.Equivalence-Induction
open import MLTT.Spartan hiding (𝟚)
open import UF.Embeddings
open import UF.KrausLemma
open import UF.Size
open import UF.Subsingletons hiding (is-subsingleton)
open import UF.SubtypeClassifier
open import UF.Univalence hiding (is-univalent)

open Locale

\end{code}

\section{Introduction}

\section{Foundations}

\begin{code}

definition-1 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-1 = _is_small

\end{code}

\begin{code}

lemma-2 : {𝓤 : Universe}
        → ((X : 𝓤 ̇) → is-subsingleton (-Σ (𝓤 ̇) (_≃_ X)))
        → is-univalent 𝓤
lemma-2 = →univalence

\end{code}

\begin{code}

definition-3 : {𝓤 : Universe} → 𝓤 ⁺  ̇ → 𝓤 ⁺  ̇
definition-3 = is-locally-small

\end{code}

\begin{code}

definition-4 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-4 = _is_small

\end{code}

\begin{code}

definition-5 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-5 = _is_small

\end{code}

\section{Locales}

\begin{code}

definition-7 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-7 = _is_small

\end{code}

\begin{code}

definition-8 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-8 = _is_small

\end{code}

\begin{code}

definition-9 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-9 = _is_small

\end{code}

\begin{code}

definition-10 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-10 = _is_small

\end{code}

\begin{code}

definition-11 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-11 = _is_small

\end{code}

\begin{code}

lemma-12 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-12 = _is_small

\end{code}

\begin{code}

definition-14 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-14 = _is_small

\end{code}

\begin{code}

definition-15 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-15 = _is_small

\end{code}

\begin{code}

definition-16 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-16 = _is_small

\end{code}

\begin{code}

remark-17 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
remark-17 = _is_small

\end{code}

\begin{code}

lemma-18 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-18 = _is_small

\end{code}

\section{Spectral and Stone Locales}

\begin{code}

definition-19 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-19 = _is_small

\end{code}

\begin{code}

lemma-20 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-20 = _is_small

\end{code}

\begin{code}

definition-21 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-21 = _is_small

\end{code}

\subsection{Spectral locales}

\begin{code}

definition-22 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-22 = _is_small

\end{code}

\begin{code}

definition-23 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-23 = _is_small

\end{code}

\begin{code}

lemma-24 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-24 = _is_small

\end{code}

\begin{code}

definition-25 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-25 = _is_small

\end{code}

\begin{code}

lemma-26 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-26 = _is_small

\end{code}

\begin{code}

definition-27 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-27 = _is_small

\end{code}

\begin{code}

lemma-28 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-28 = _is_small

\end{code}

\begin{code}

corollary-29 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
corollary-29 = _is_small

\end{code}

\begin{code}

lemma-30 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-30 = _is_small

\end{code}

\begin{code}

lemma-31 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-31 = _is_small

\end{code}

\begin{code}

definition-32 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-32 = _is_small

\end{code}

\begin{code}

lemma-33 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-33 = _is_small

\end{code}

\begin{code}

lemma-34 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-34 = _is_small

\end{code}

\begin{code}

the-theorem-from-§4∙1 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
the-theorem-from-§4∙1 = _is_small

\end{code}

\begin{code}

example-35 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
example-35 = _is_small

\end{code}

\begin{code}

lemma-36 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-36 = _is_small

\end{code}

\begin{code}

proposition-37 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
proposition-37 = _is_small

\end{code}

\subsection{Stone locales}

\begin{code}

definition-38 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-38 = _is_small

\end{code}

\begin{code}

definition-39 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-39 = _is_small

\end{code}

\begin{code}

lemma-40 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-40 = _is_small

\end{code}

\begin{code}

definition-41 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-41 = _is_small

\end{code}

\begin{code}

lemma-42 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-42 = _is_small

\end{code}

\begin{code}

lemma-43 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-43 = _is_small

\end{code}

\begin{code}

lemma-44 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-44 = _is_small

\end{code}

\begin{code}

corollary-45 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
corollary-45 = _is_small

\end{code}

\begin{code}

corollary-46 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
corollary-46 = _is_small

\end{code}

\begin{code}

definition-47 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
definition-47 = _is_small

\end{code}

\begin{code}

lemma-48 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-48 = _is_small

\end{code}

\begin{code}

lemma-49 : {𝓤 : Universe} → 𝓤  ̇ → (𝓥 : Universe) → (𝓥 ⁺) ⊔ 𝓤 ̇
lemma-49 = _is_small

\end{code}

\section{Posetal Adjoint Functor Theorem}

\section{Meet-semilattice of Scott continuous nuclei}

\section{Joins in the frame of Scott continuous nuclei}

\section{The coreflection property of Patch}

\section{Summary and discussion}
