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

open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤
open import DomainTheory.Basics.Dcpo    pt fe 𝓤 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Basics.Miscelanea pt fe 𝓤
open import DomainTheory.Basics.Pointed pt fe 𝓤 renaming (⊥ to ⊥∙)
open import DomainTheory.Basics.WayBelow pt fe 𝓤
open import DomainTheory.Lifting.LiftingSet pt fe 𝓤 pe
open import DomainTheory.Lifting.LiftingSetAlgebraic pt pe fe 𝓤
open import Lifting.Construction 𝓤
open import Lifting.Miscelanea-PropExt-FunExt 𝓤 pe fe
open import Lifting.UnivalentPrecategory 𝓤 (𝟙 {𝓤})
open import Locales.Compactness pt fe
open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.Frame pt fe hiding (𝟚; is-directed)
open import Locales.InitialFrame pt fe
open import Locales.Sierpinski.Definition 𝓤 pe pt fe sr
open import Locales.Sierpinski.Properties 𝓤 pe pt fe sr
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import Locales.Stone pt fe sr
open import MLTT.List hiding ([_])
open import Slice.Family
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Logic
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
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
open PatchConstruction 𝕊 𝕊-is-spectral

ump-for-patch-of-𝕊 : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
                   → is-stone X holds
                   → (𝒻@(f , _) : X ─c→ 𝕊)
                   → is-spectral-map 𝕊 X 𝒻 holds
                   → ∃! 𝒻⁻@(f⁻ , _) ꞉ X ─c→ Patch-𝕊 ,
                      ((U : ⟨ 𝒪 𝕊 ⟩) → f U ＝ f⁻ ‘ U ’)
ump-for-patch-of-𝕊 = ump-of-patch 𝕊 𝕊-is-spectral 𝕊-has-small-𝒦

\end{code}

We show that there are exactly four compact opens in `Patch(𝕊)`.

The first one: the closed nucleus on the top element of `𝕊`.

\begin{code}

closed-𝟏 : ⟨ 𝒪 Patch-𝕊 ⟩
closed-𝟏 = ‘ 𝟏[ 𝒪 𝕊 ] ’

\end{code}

The second one: the closed nucleus on the bottom element of `𝕊`.

\begin{code}

closed-𝟎 : ⟨ 𝒪 Patch-𝕊 ⟩
closed-𝟎 = ‘ 𝟎[ 𝒪 𝕊 ] ’

\end{code}

This is the same thing as the bottom nucleus.

\begin{code}

closed-𝟎-is-bottom : closed-𝟎 ＝ 𝟎[ 𝒪 Patch-𝕊 ]
closed-𝟎-is-bottom =
 perfect-nuclei-eq closed-𝟎 𝟎[ 𝒪 Patch-𝕊 ] (dfunext fe †)
 where
  † : closed-𝟎 $_ ∼ 𝟎[ 𝒪 Patch-𝕊 ] $_
  † U = 𝟎[ 𝒪 𝕊 ] ∨[ 𝒪 𝕊 ] U    ＝⟨ 𝟎-right-unit-of-∨ (𝒪 𝕊) U ⟩
        U                      ＝⟨ 𝟎-is-id U ⁻¹ ⟩
        𝟎[ 𝒪 Patch-𝕊 ] .pr₁ U  ∎

\end{code}

The third one: the closed nucleus on the singleton set `{ ⊤ }`.

\begin{code}

closed-truth : ⟨ 𝒪 Patch-𝕊 ⟩
closed-truth = ‘ truth ’

\end{code}

The fourth one: the _open_ nucleus on the singleton `{ ⊤ }`.

\begin{code}

open PatchStoneᴰ 𝕊 𝕊-is-spectralᴰ
open BasisOfPatch 𝕊 𝕊-is-spectralᴰ
open OpenNucleus 𝕊 𝕊-is-spectralᴰ 𝕊-has-small-𝒦

truthₖ : 𝒦 𝕊
truthₖ = truth , truth-is-compact

open-truth : ⟨ 𝒪 Patch-𝕊 ⟩
open-truth = ¬‘ truthₖ ’

\end{code}

We now write down a type family expressing that a given open is equal to one
of these four opens.

\begin{code}

equal-to-one-of-the-four-compact-opensₚ : (U : ⟨ 𝒪 Patch-𝕊 ⟩ ) → 𝓤 ⁺  ̇
equal-to-one-of-the-four-compact-opensₚ U =
 (U ＝ closed-𝟎) + (U ＝ closed-truth) + (U ＝ open-truth) + (U ＝ closed-𝟏)

basis-tetrachotomy-for-Patch-𝕊
 : (i : index ℬ-patch-↑)
 → equal-to-one-of-the-four-compact-opensₚ (ℬ-patch-↑ [ i ])
basis-tetrachotomy-for-Patch-𝕊 []       = inl †
 where
  goal : ℬ-patch-↑ [ [] ] ＝ 𝟎[ 𝒪 Patch-𝕊 ]
  goal = refl

  † : 𝟎[ 𝒪 Patch-𝕊 ] ＝ closed-𝟎
  † = closed-𝟎-is-bottom ⁻¹
basis-tetrachotomy-for-Patch-𝕊 (i ∷ is) = {!!}

\end{code}
