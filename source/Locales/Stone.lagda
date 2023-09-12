Ayberk Tosun, 11 September 2023

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.FunExt
open import UF.UA-FunExt

module Locales.Stone (pt : propositional-truncations-exist)
                     (fe : Fun-Ext)                           where

\end{code}

Importation of foundational UF stuff.

\begin{code}

open import Slice.Family
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

Importations of other locale theory modules.

\begin{code}

open import Locales.AdjointFunctorTheoremForFrames
open import Locales.Frame            pt fe
open import Locales.WayBelow         pt fe
open import Locales.Compactness      pt fe
open import Locales.Complements      pt fe
open import Locales.GaloisConnection pt fe
open import Locales.InitialFrame     pt fe
open import Locales.ZeroDimensionality pt fe

open Locale

\end{code}

\begin{code}

is-stone : (X : Locale 𝓤 𝓥 𝓦) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-stone X = is-compact X ∧ is-zero-dimensional (𝒪 X)

\end{code}

\begin{code}
