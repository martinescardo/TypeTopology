Ayberk Tosun, 8 September 2023


\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.FunExt
open import UF.EquivalenceExamples
open import MLTT.List hiding ([_])
open import MLTT.Pi
open import Slice.Family
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Logic

module Locales.Point (pt : propositional-truncations-exist)
                     (fe : Fun-Ext)                           where

open import Locales.Frame pt fe
open import Locales.Compactness pt fe

\end{code}

\begin{code}

is-completely-prime-filter : Locale 𝓤 𝓥 𝓦 → {!!}
is-completely-prime-filter = {!!}

\end{code}
