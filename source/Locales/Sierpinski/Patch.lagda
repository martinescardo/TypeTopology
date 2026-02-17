---
title:          The patch locale of the Sierpiński locale
author:         Ayberk Tosun
date-completed: 2024-02-12
---

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons

module Locales.Sierpinski.Patch
        (𝓤  : Universe)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
       where

open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.Frame pt fe hiding (𝟚; is-directed)
open import Locales.Sierpinski.Definition 𝓤 pe pt fe sr
open import Locales.Sierpinski.Properties 𝓤 pe pt fe sr
open import Locales.Spectrality.SpectralMap pt fe
open import Locales.Stone pt fe sr
open import UF.SubtypeClassifier

open ContinuousMaps
open FrameHomomorphismProperties
open FrameHomomorphisms
open Locale
open PropositionalTruncation pt

\end{code}

We conclude by constructing the patch of Sierpiński.

\begin{code}

open import Locales.ScottLocale.ScottLocalesOfScottDomains pt fe sr 𝓤

open SpectralScottLocaleConstruction 𝕊𝓓 𝕊𝓓-has-least hscb 𝕊𝓓-satisfies-dc 𝕊𝓓-bounded-complete pe

open import Locales.PatchLocale pt fe sr

open SmallPatchConstruction 𝕊 𝕊-is-spectralᴰ renaming (SmallPatch to Patch-𝕊)

patch-of-𝕊 : Locale (𝓤 ⁺) 𝓤 𝓤
patch-of-𝕊 = Patch-𝕊

\end{code}

The universal property of Patch then specializes to the following.

\begin{code}

open import Locales.UniversalPropertyOfPatch pt fe sr

open import Locales.PatchProperties pt fe sr

open ClosedNucleus 𝕊 𝕊-is-spectral
open ContinuousMaps

ump-for-patch-of-𝕊 : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
                   → is-stone X holds
                   → (𝒻@(f , _) : X ─c→ 𝕊)
                   → is-spectral-map 𝕊 X 𝒻 holds
                   → ∃! 𝒻⁻@(f⁻ , _) ꞉ X ─c→ Patch-𝕊 ,
                      ((U : ⟨ 𝒪 𝕊 ⟩) → f U ＝ f⁻ ‘ U ’)
ump-for-patch-of-𝕊 = ump-of-patch 𝕊 𝕊-is-spectral 𝕊-has-small-𝒦

\end{code}
