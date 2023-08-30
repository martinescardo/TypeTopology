Ayberk Tosun, 17 August 2023.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons
open import UF.SubTypeClassifier

module Locales.PatchOfOmega (pt : propositional-truncations-exist)
                            (fe : Fun-Ext)
                            (𝓤  : Universe)
                            (pe : propext 𝓤)
                             where

open import Locales.Frame        pt fe
open import Locales.PatchLocale  pt fe
open import Locales.InitialFrame pt fe

Ω-frm : Frame (𝓤 ⁺) 𝓤 𝓤
Ω-frm = 𝟎-𝔽𝕣𝕞 pe

\end{code}

This is the terminal locale which I denote by `𝟏-loc`

\begin{code}

𝟏-loc : Locale (𝓤 ⁺) 𝓤 𝓤
𝟏-loc = record { ⟨_⟩ₗ = ⟨ Ω-frm ⟩ ; frame-str-of = pr₂ Ω-frm }

\end{code}

We know that `Ω-Frm` is spectral.

\begin{code}

open import Locales.CompactRegular pt fe
open SpectralityOfTheInitialFrame 𝓤 pe

Ω-is-spectral : is-spectral (𝟎-𝔽𝕣𝕞 pe) holds
Ω-is-spectral = 𝟎-𝔽𝕣𝕞-is-spectral

\end{code}

This means that we can easily compute the patch of `Ω`.

\begin{code}

open PatchConstruction 𝟏-loc Ω-is-spectral renaming (Patch to patch-Ω)

patch-of-Ω : Locale (𝓤 ⁺) (𝓤 ⁺) 𝓤
patch-of-Ω = patch-Ω

\end{code}

TODO: Prove that this is the frame of booleans.
