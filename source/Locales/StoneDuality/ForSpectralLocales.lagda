--------------------------------------------------------------------------------
title:          Stone duality for spectral locales
author:         Ayberk Tosun
date-started:   2024-04-12
--------------------------------------------------------------------------------

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification --exact-split --double-check #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

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
open import Locales.ContinuousMap.Homeomorphism-Definition pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.LocaleOfSpectra fe pe pt
open import Locales.DistributiveLattice.LocaleOfSpectra-Properties fe pe pt
open import Locales.Spectrality.LatticeOfCompactOpens ua pt sr
open import Locales.Frame pt fe
open import Locales.SIP.FrameSIP
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Compactness pt fe
open import Slice.Family
open import UF.Equiv
open import UF.Logic
open import UF.SubtypeClassifier
open import Locales.DistributiveLattice.Resizing ua pt sr

open AllCombinators pt fe
open FrameHomomorphismProperties
open FrameHomomorphisms
open Locale

\end{code}

We denote by `spec L` the spectrum (the locale defined by the frame of ideals)
of a distributive lattice `L`.

\begin{code}

open DefnOfFrameOfIdeal

spec : DistributiveLattice 𝓤 → Locale (𝓤 ⁺) 𝓤 𝓤
spec = locale-of-spectra

\end{code}

A locale `X` is called `spectral·` if it is homeomorphic to the spectrum of some
distributive lattice `L `.

\begin{code}

is-spectral· : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Ω (𝓤 ⁺)
is-spectral· {𝓤} X = Ǝ L ꞉ DistributiveLattice 𝓤 , X ≅c≅ spec L

\end{code}

This definition uses `∃` instead of `Σ`, because even though the distributive
lattice of compact opens is unique, the homeomorphism involved need not be.

TODO: add the definition that specifies the equivalence and is therefore
naturally propositional.

Because `spec L` is a spectral locale (with a small basis), any locale `X` that
is homeomorphic to `spec L` for some distributive lattice `L` must be spectral
(with small basis).

\begin{code}

spectral·-implies-spectral-with-small-basis
 : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
 → is-spectral· X holds
 → is-spectral-with-small-basis ua X holds
spectral·-implies-spectral-with-small-basis {𝓤} X =
 ∥∥-rec (holds-is-prop (is-spectral-with-small-basis ua X)) †
  where
   open PropositionalTruncation pt

   † : (Σ L ꞉ DistributiveLattice 𝓤 , X ≅c≅ spec L)
     → is-spectral-with-small-basis ua X holds
   † (L , 𝒽) = transport (_holds ∘ is-spectral-with-small-basis ua) q 𝕤
    where
     open Spectrality sr L

     p : 𝒪 (spec L) ＝ 𝒪 X
     p = isomorphic-frames-are-equal ua pt sr (𝒪 (spec L)) (𝒪 X) 𝒽

     q : spec L ＝ X
     q = to-locale-＝ (spec L) X p

     𝕤 : is-spectral-with-small-basis ua (spec L) holds
     𝕤 = spec-L-is-spectral , spec-L-has-small-𝒦

\end{code}
