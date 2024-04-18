--------------------------------------------------------------------------------
title:          Stone duality for spectral locales
author:         Ayberk Tosun
date-started:   2024-04-12
--------------------------------------------------------------------------------

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.UA-FunExt
open import UF.Univalence
open import UF.Subsingletons

module Locales.StoneDuality.ForSpectralLocales
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

private
 fe : Fun-Ext
 fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

 pe : Prop-Ext
 pe {𝓤} = univalence-gives-propext (ua 𝓤)

open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.ContinuousMap.FrameIsomorphism-Definition pt fe
open import Locales.ContinuousMap.Homeomorphism-Definition pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.LocaleOfSpectra fe pe pt
open import Locales.DistributiveLattice.LocaleOfSpectra-Properties fe pe pt
open import Locales.Frame pt fe
open import Locales.SIP.FrameSIP
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.LatticeOfCompactOpens ua pt sr
open import Locales.Spectrality.SpectralLocale
open import Slice.Family
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.Logic
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open AllCombinators pt fe
open FrameHomomorphismProperties
open FrameHomomorphisms
open Locale

\end{code}

We denote by `spec L` the locale of spectra of a distributive lattice `L`.

\begin{code}

open DefnOfFrameOfIdeal

spec : DistributiveLattice 𝓤 → Locale (𝓤 ⁺) 𝓤 𝓤
spec = locale-of-spectra

\end{code}

A locale `X` is said to be a _locale of spectra_ if it's homeomorphic to the
locale of spectra of some distributive lattice `L `.

\begin{code}

is-locale-of-spectra : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → 𝓤 ⁺  ̇
is-locale-of-spectra {𝓤} X = Σ L ꞉ DistributiveLattice 𝓤 , X ≅c≅ spec L

\end{code}
