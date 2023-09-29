Ayberk Tosun, 29 September 2023

This module contains a definition of the Scott locale of a dcpo, using the definition of
dcpo from the `DomainTheory` development due to Tom de Jong.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.List hiding ([_])
open import MLTT.Pi
open import MLTT.Spartan
open import Slice.Family
open import UF.Base
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.Univalence

\end{code}

We assume the existence of propositional truncations as well as function extensionality.

\begin{code}

module Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥  : Universe)
        where

open Universal fe
open Implication fe
open Existential pt
open Conjunction
open import Locales.Frame pt fe
open import DomainTheory.Basics.Dcpo pt fe 𝓥 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Topology.ScottTopology pt fe 𝓥

open PropositionalTruncation pt

\end{code}

\begin{code}

\end{code}
