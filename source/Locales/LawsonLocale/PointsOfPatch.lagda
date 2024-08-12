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
open import Locales.Stone pt fe sr
open import Locales.StoneImpliesSpectral pt fe sr
open import Locales.TerminalLocale.Properties pt fe sr
open import Locales.UniversalPropertyOfPatch pt fe sr
open import Locales.ZeroDimensionality pt fe sr
open import NotionsOfDecidability.Decidable
open import NotionsOfDecidability.SemiDecidable fe pe pt
open import Slice.Family
open import UF.Base
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
 open PatchStoneᴰ σ⦅𝓓⦆ scott-locale-spectralᴰ

 patch-σ𝓓 : Locale (𝓤 ⁺) 𝓤 𝓤
 patch-σ𝓓 = SmallPatch

 patch-σ𝓓-stoneᴰ : stoneᴰ patch-σ𝓓
 patch-σ𝓓-stoneᴰ = patchₛ-is-compact , patchₛ-zero-dimensionalᴰ

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

 to-patch-point : Spectral-Point σ⦅𝓓⦆ → Spectral-Point patch-σ𝓓
 to-patch-point ℱ = to-spectral-point patch-σ𝓓 (𝓅 , †)
  where
   open Spectral-Point ℱ renaming (point to F)
   open continuous-maps-of-stone-locales (𝟏Loc pe) patch-σ𝓓 (𝟏-stoneᴰ pe) patch-σ𝓓-stoneᴰ

   𝕤 : is-spectral-map σ⦅𝓓⦆ (𝟏Loc pe) F holds
   𝕤 K κ = point-preserves-compactness K κ

   𝓅 : 𝟏Loc pe ─c→ patch-σ𝓓
   𝓅 = ∃!-witness (patch-ump F 𝕤)

   † : is-spectral-map patch-σ𝓓 (𝟏Loc pe) 𝓅 holds
   † = continuous-maps-between-stone-locales-are-spectral 𝓅

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

\begin{code}

 to-patch-point-qinv : qinv to-patch-point
 to-patch-point-qinv = to-spectral-point′ , † , ‡
  where
   open ContinuousMaps
   open ContinuousMapNotation (𝟏Loc pe) patch-σ𝓓

   † : to-spectral-point′ ∘ to-patch-point ∼ id
   † ℱ = to-spectral-point-＝ σ⦅𝓓⦆ (to-spectral-point′ (to-patch-point ℱ)) ℱ ♢
    where
     open Spectral-Point using (point; point-fn; point-preserves-compactness)
     open Spectral-Point ℱ using () renaming (point-fn to F)

     𝕤 : is-spectral-map σ⦅𝓓⦆ (𝟏Loc pe) (point ℱ) holds
     𝕤 K κ = point-preserves-compactness ℱ K κ

     γ : (U : ⟨ 𝒪 σ⦅𝓓⦆ ⟩)
       → point-fn (to-spectral-point′ (to-patch-point ℱ)) U ＝ F U
     γ U = pr₂ (description (patch-ump (point ℱ) 𝕤)) U ⁻¹

     ♢ : point-fn (to-spectral-point′ (to-patch-point ℱ)) ＝ F
     ♢ = dfunext fe γ

   ‡ : to-patch-point ∘ to-spectral-point′ ∼ id
   ‡ 𝓅 = to-spectral-point-＝'
          patch-σ𝓓
          (to-patch-point (to-spectral-point′ 𝓅))
          𝓅
          (γ ⁻¹)
    where
     open Spectral-Point 𝓅 renaming (point-fn to p⋆; point to 𝓅⋆)
     open FrameHomomorphismProperties (𝒪 (𝟏Loc pe)) (𝒪 patch-σ𝓓)

     𝓅₀ : 𝟏Loc pe ─c→ σ⦅𝓓⦆
     𝓅₀ = cont-comp (𝟏Loc pe) patch-σ𝓓 σ⦅𝓓⦆ ϵ 𝓅⋆

     p₀ = pr₁ 𝓅₀

     𝕤 : is-spectral-map σ⦅𝓓⦆ (𝟏Loc pe) 𝓅₀ holds
     𝕤 K κ = point-preserves-compactness ‘ K ’ (ϵ-is-a-spectral-map K κ)

     υ : ∃! 𝓅₀⁻ ꞉ 𝟏Loc pe ─c→ patch-σ𝓓 , ((U : ⟨ 𝒪 σ⦅𝓓⦆ ⟩) → p₀ U  ＝ 𝓅₀⁻ ⋆∙ ‘ U ’ )
     υ = patch-ump 𝓅₀ 𝕤

     𝓅₀⁻ : 𝟏Loc pe ─c→ patch-σ𝓓
     𝓅₀⁻ = ∃!-witness υ

     foo : (U : ⟨ 𝒪 σ⦅𝓓⦆ ⟩) → p₀ U ＝ p⋆ ‘ U ’
     foo U = refl

     γ : 𝓅⋆ ＝ 𝓅₀⁻
     γ = pr₁ (from-Σ-＝ (∃!-uniqueness υ 𝓅⋆ foo)) ⁻¹

\end{code}
