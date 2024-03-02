--------------------------------------------------------------------------------
title:        Properties of ideals
author:       Ayberk Tosun
date-started: 2024-03-02
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Locales.DistributiveLattice.Ideal-Properties
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Ideal pt fe pe
open import Locales.DistributiveLattice.LocaleOfSpectra fe pe pt
open import Locales.DistributiveLattice.Properties fe pt
open import Locales.Frame pt fe
open import MLTT.List
open import MLTT.Spartan
open import UF.Base
open import UF.Equiv hiding (_■)
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.SubtypeClassifier

open AllCombinators pt fe hiding (_∨_)
open PropositionalTruncation pt hiding (_∨_)

\end{code}

\begin{code}

module IdealProperties (L : DistributiveLattice 𝓤) where

 open DistributiveLattice L
 open IdealNotation L
 open DefnOfFrameOfIdeal  L

 contains-𝟏-implies-above-𝟏 : (I : Ideal L) → 𝟏 ∈ⁱ I → (𝟏ᵢ ⊆ᵢ I) holds
 contains-𝟏-implies-above-𝟏 I μ₁ x μ₂ =
  I-is-downward-closed x 𝟏 (𝟏ᵈ-is-top L x) μ₁
   where
    open Ideal I using (I-is-downward-closed)

 above-𝟏-implies-contains-𝟏 : (I : Ideal L) → (𝟏ᵢ ⊆ᵢ I) holds → 𝟏 ∈ⁱ I
 above-𝟏-implies-contains-𝟏 I φ = φ 𝟏 (≤-is-reflexive (poset-ofᵈ L) 𝟏)

\end{code}
