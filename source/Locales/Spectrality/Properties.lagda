Ayberk Tosun, 13 September 2023

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
open import UF.SubtypeClassifier
open import UF.Subsingletons-FunExt
open import UF.Logic

module Locales.Spectrality.Properties (pt : propositional-truncations-exist)
                                      (fe : Fun-Ext) where

open import Locales.Frame pt fe
open import Locales.Compactness pt fe

open PropositionalTruncation pt

open AllCombinators pt fe

open Locale

\end{code}
