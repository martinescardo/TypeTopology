---
title:          Sharp elements and the points of patch
author:         Ayberk Tosun
date-started:   2024-08-04
---

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.List hiding ([_])
open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

module Locales.LawsonLocale.PointsOfPatch
        (𝓤  : Universe)
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

private
 fe : Fun-Ext
 fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

 pe : Prop-Ext
 pe {𝓤} = univalence-gives-propext (ua 𝓤)

open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓤
open import DomainTheory.BasesAndContinuity.CompactBasis pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤
open import DomainTheory.BasesAndContinuity.ScottDomain pt fe 𝓤
open import DomainTheory.Basics.Dcpo pt fe 𝓤 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Basics.WayBelow pt fe 𝓤
open import DomainTheory.Topology.ScottTopology pt fe 𝓤
open import DomainTheory.Topology.ScottTopologyProperties pt fe 𝓤
open import Locales.Clopen pt fe sr
open import Locales.CompactRegular pt fe using (clopens-are-compact-in-compact-frames)
open import Locales.Compactness pt fe hiding (is-compact)
open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.Frame pt fe
open import Locales.InitialFrame pt fe hiding (_⊑_)
open import Locales.LawsonLocale.CompactElementsOfPoint 𝓤 fe pe pt sr
open import Locales.PatchLocale pt fe sr
open import Locales.PatchProperties pt fe sr
open import Locales.PerfectMaps pt fe
open import Locales.Point.Definition pt fe
open import Locales.Point.SpectralPoint-Definition pt fe pe
open import Locales.ScottLocale.Definition pt fe 𝓤
open import Locales.ScottLocale.Properties pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfScottDomains pt fe sr 𝓤
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralMap pt fe
open import Locales.Spectrality.SpectralityOfOmega pt fe sr 𝓤 pe
open import Locales.TerminalLocale.Properties pt fe sr
open import Locales.UniversalPropertyOfPatch pt fe sr
open import Locales.ZeroDimensionality pt fe sr
open import NotionsOfDecidability.Decidable
open import NotionsOfDecidability.SemiDecidable fe pe pt
open import Slice.Family
open import UF.Equiv
open import UF.Logic
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier renaming (⊥ to ⊥ₚ)

open AllCombinators pt fe
open DefinitionOfScottDomain
open Locale
open PerfectMaps
open PropositionalTruncation pt hiding (_∨_)

\end{code}

\begin{code}

module points-of-patch-are-spectral-points
        (𝓓  : DCPO {𝓤 ⁺} {𝓤})
        (hl : has-least (underlying-order 𝓓))
        (sd : is-scott-domain 𝓓 holds)
        (dc : decidability-condition 𝓓)
       where

 zd : zero-dimensionalᴰ {𝓤 ⁺} (𝒪 (𝟏Loc pe))
 zd = 𝟏-zero-dimensionalᴰ pe

 open SpectralScottLocaleConstruction₂ 𝓓 ua hl sd dc pe
 open Notion-Of-Spectral-Point
 open SmallPatchConstruction σ⦅𝓓⦆ scott-locale-spectralᴰ
 open Preliminaries
 open UniversalProperty σ⦅𝓓⦆ (𝟏Loc pe) scott-locale-spectralᴰ zd 𝟎Frm-is-compact
 open ContinuousMaps
 open ClosedNucleus σ⦅𝓓⦆ scott-locale-is-spectral
 open Epsilon σ⦅𝓓⦆ scott-locale-spectralᴰ

 patch-σ𝓓 : Locale (𝓤 ⁺) 𝓤 𝓤
 patch-σ𝓓 = SmallPatch

 patch-ump : (𝓅 : 𝟏Loc pe ─c→ σ⦅𝓓⦆)
           → is-spectral-map σ⦅𝓓⦆ (𝟏Loc pe) 𝓅 holds
           → ∃! 𝒻⁻ ꞉ 𝟏Loc pe ─c→ patch-σ𝓓 , ((U : ⟨ 𝒪 σ⦅𝓓⦆ ⟩) → 𝓅 .pr₁ U  ＝ 𝒻⁻ .pr₁ ‘ U ’ )
 patch-ump 𝓅 σ = ump-of-patch
                  σ⦅𝓓⦆
                  scott-locale-is-spectral
                  scott-locale-has-small-𝒦
                  (𝟏Loc pe)
                  (𝟏-is-stone pe)
                  𝓅
                  σ

 to-patch-point : Spectral-Point σ⦅𝓓⦆ → Point patch-σ𝓓
 to-patch-point ℱ = ∃!-witness (patch-ump F 𝕤)
  where
   open Spectral-Point ℱ renaming (point to F)

   𝕤 : is-spectral-map σ⦅𝓓⦆ (𝟏Loc pe) F holds
   𝕤 K κ = point-preserves-compactness K κ

\end{code}

The proof below should be placed in a more appropriate place.

\begin{code}

 ϵ-is-a-spectral-map : is-spectral-map σ⦅𝓓⦆ patch-σ𝓓 ϵ holds
 ϵ-is-a-spectral-map =
  perfect-maps-are-spectral
   patch-σ𝓓
   σ⦅𝓓⦆
   ∣ spectralᴰ-implies-basisᴰ σ⦅𝓓⦆ scott-locale-spectralᴰ ∣
   ϵ
   ϵ-is-a-perfect-map

\end{code}

\begin{code}

 to-spectral-point′ : Spectral-Point patch-σ𝓓 → Spectral-Point σ⦅𝓓⦆
 to-spectral-point′ ℱ⁻ₛ = to-spectral-point σ⦅𝓓⦆ (ℱ , 𝕤)
  where
   open Spectral-Point ℱ⁻ₛ renaming (point to ℱ⁻)

   ℱ : 𝟏Loc pe ─c→ σ⦅𝓓⦆
   ℱ = cont-comp (𝟏Loc pe) patch-σ𝓓 σ⦅𝓓⦆ ϵ ℱ⁻

   𝕤 : is-spectral-map σ⦅𝓓⦆ (𝟏Loc pe) ℱ holds
   𝕤 K κ = point-preserves-compactness ‘ K ’ (ϵ-is-a-spectral-map K κ)

\end{code}
