Ayberk Tosun.

Started on: 2023-10-25.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import Slice.Family
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Powerset-MultiUniverse

module Locales.ScottLocale.ScottLocalesOfScottDomains
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓤  : Universe) where

open import Locales.Frame

open Universal fe
open Implication fe
open Existential pt
open Conjunction

open Locale

open PropositionalTruncation pt

\end{code}
