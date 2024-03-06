--------------------------------------------------------------------------------
title:          Properties of the locale of spectra
author:         Ayberk Tosun
date-started:   2024-03-01
--------------------------------------------------------------------------------

We define the locale of spectra over a distributive lattice `L`, the defining
frame of which is the frame of ideals over `L`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons

module Locales.DistributiveLattice.LocaleOfSpectra-Properties
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Locales.Compactness pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Ideal pt fe pe
open import Locales.DistributiveLattice.Ideal-Properties pt fe pe
open import Locales.DistributiveLattice.LocaleOfSpectra fe pe pt
open import Locales.DistributiveLattice.Properties fe pt
open import Locales.Frame pt fe
open import MLTT.Fin hiding (𝟎; 𝟏)
open import MLTT.List hiding ([_])
open import MLTT.Spartan
open import Slice.Family
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.SubtypeClassifier

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)
open PropositionalSubsetInclusionNotation fe
open PropositionalTruncation pt hiding (_∨_)
open Locale

\end{code}

We work with a fixed distributive lattice `L` in this module.

\begin{code}

module Spectrality (L : DistributiveLattice 𝓤) where

 open DefnOfFrameOfIdeal  L
 open DistributiveLattice L renaming (X-is-set to σ)
 open IdealNotation L
 open IdealProperties L

\end{code}

We abbreviate `locale-of-spectra` to `spec-L`.

\begin{code}

 spec-L : Locale (𝓤 ⁺) 𝓤 𝓤
 spec-L = locale-of-spectra

\end{code}

The locale of spectra of is a compact locale.

\begin{code}

 locale-of-spectra-is-compact : is-compact spec-L holds
 locale-of-spectra-is-compact S δ p =
  ∥∥-rec ∃-is-prop † (p 𝟏 (𝟏ᵈ-is-top L 𝟏))
   where
    † : Σ xs ꞉ List X , xs ◁ S × (𝟏 ＝ join-listᵈ L xs)
      → ∃ i ꞉ index S , (𝟏[ 𝒪 spec-L ] ≤[ poset-of (𝒪 spec-L) ] S [ i ]) holds
    † (xs , c , r) = ∥∥-rec ∃-is-prop ‡ (finite-subcover S xs δ c)
     where
      ‡ : Σ k ꞉ index S , join-listᵈ L xs ∈ⁱ (S [ k ])
        → ∃ i ꞉ index S , (𝟏[ 𝒪 spec-L ] ≤[ poset-of (𝒪 spec-L) ] S [ i ]) holds
      ‡ (k , p) = ∣ k , contains-𝟏-implies-above-𝟏 (S [ k ]) μ ∣
       where
        μ : 𝟏 ∈ⁱ (S [ k ])
        μ = transport (λ - → - ∈ⁱ (S [ k ])) (r ⁻¹) p

\end{code}
