---
title:          Distributive lattice of compact opens
author:         Ayberk Tosun
date-started:   2024-02-24
date-completed: 2024-02-27
---

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.List hiding ([_])
open import MLTT.Pi
open import MLTT.Spartan
open import Slice.Family
open import UF.Base
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.FunExt
open import UF.ImageAndSurjection
open import UF.Logic
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.UA-FunExt
open import UF.Univalence

module Locales.Spectrality.LatticeOfCompactOpens-Duality
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

private
 fe : Fun-Ext
 fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

 pe : Prop-Ext
 pe {𝓤} = univalence-gives-propext (ua 𝓤)

open import Locales.Compactness pt fe
open import Locales.Spectrality.LatticeOfCompactOpens ua pt sr
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Homomorphism fe pt
open import Locales.DistributiveLattice.LocaleOfSpectra fe pe pt
open import Locales.Frame pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import UF.Equiv

open AllCombinators pt fe
open Locale
open PropositionalTruncation pt

\end{code}

We fix a large and locally small locale `X`, assumed to be spectral with a small
type of compact opens.

\begin{code}

module 𝒦-Duality (X  : Locale (𝓤 ⁺) 𝓤 𝓤)
                 (σ₀ : is-spectral-with-small-basis ua X holds) where

 open 𝒦-Lattice X σ₀

\end{code}

We define some shorthand notation to simplify the proofs.

\begin{code}

 σ : is-spectral X holds
 σ = ssb-implies-spectral ua X σ₀

 𝟏-is-compact : is-compact-open X 𝟏[ 𝒪 X ] holds
 𝟏-is-compact = spectral-locales-are-compact X σ

 𝟏ₖ : 𝒦 X
 𝟏ₖ = 𝟏[ 𝒪 X ] , 𝟏-is-compact

\end{code}

\begin{code}

\end{code}

\begin{code}

 spec-

 forward₀ : ⟨ 𝒪 X ⟩ → {!!}
 forward₀ = {!!}

\end{code}
