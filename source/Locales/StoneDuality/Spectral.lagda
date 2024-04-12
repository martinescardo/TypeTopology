--------------------------------------------------------------------------------
title:          Stone duality for spectral locales
author:         Ayberk Tosun
date-started:   2024-04-12
--------------------------------------------------------------------------------

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.UA-FunExt
open import UF.Univalence
open import UF.Subsingletons

module Locales.StoneDuality.Spectral
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
open import Locales.ContinuousMap.Homeomorphism-Definition pt fe
open import Locales.Spectrality.SpectralLocale
open import Locales.Spectrality.LatticeOfCompactOpens ua pt sr
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.LocaleOfSpectra fe pe pt
open import Locales.SmallBasis pt fe sr
open import Locales.Frame pt fe
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

\end{code}

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

\begin{code}

-- locale-of-spectra-implies-is-spectral : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
--                                       → is-locale-of-spectra X
--                                       → is-spectral-with-small-basis ua X holds
-- locale-of-spectra-implies-is-spectral X (L , 𝒽) = {!!}

\end{code}

\begin{code}

-- spectral-implies-is-locale-of-spectra : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
--                                       → is-spectral-with-small-basis ua X holds
--                                       → is-locale-of-spectra X
-- spectral-implies-is-locale-of-spectra X 𝕤 = {!𝒦⦅X⦆!} , {!!}
--  where
--   open 𝒦-Lattice X 𝕤

\end{code}
