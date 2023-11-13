Ayberk Tosun, 17 August 2023.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.Size

module Locales.PatchOfOmega (pt : propositional-truncations-exist)
                            (fe : Fun-Ext)
                            (sr : Set-Replacement pt)
                            (𝓤  : Universe)
                            (pe : propext 𝓤)
                             where

open import Locales.Frame                          pt fe
open import Locales.Spectrality.SpectralLocale     pt fe
open import Locales.Spectrality.SpectralityOfOmega pt fe sr
open import Locales.PatchLocale                    pt fe sr
open import Locales.InitialFrame                   pt fe

\end{code}

This is the terminal locale which I denote by `𝟏-loc`

\begin{code}

𝟏L : Locale (𝓤 ⁺) 𝓤 𝓤
𝟏L = 𝟏-loc 𝓤 pe

\end{code}

We know that `Ω-Frm` is spectral.

\begin{code}

open Spectrality-of-𝟎 𝓤 pe

Ω-is-spectral :  is-spectral 𝟏L holds
Ω-is-spectral = 𝟎-𝔽𝕣𝕞-is-spectral 𝓤 pe

\end{code}

This means that we can easily compute the patch of `Ω`.

\begin{code}

open PatchConstruction 𝟏L Ω-is-spectral renaming (Patch to patch-Ω)

patch-of-Ω : Locale (𝓤 ⁺) (𝓤 ⁺) 𝓤
patch-of-Ω = patch-Ω

\end{code}
