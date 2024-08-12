---
title:          Sharp elements and the points of patch
author:         Ayberk Tosun
date-started:   2024-08-04
---

We prove that the sharp elements of a Scott domain `𝓓` are in bijection with the
points of `Patch(Scott(𝓓))`.

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

In the module below, we show that points `𝟏 → Patch(Scott(𝓓))` are in
bijection with spectral points `𝟏 → Scott(𝓓)`. This is done by constructing
an equivalence
```
Point(Patch(Scott(𝓓))) ≃ Spectral-Point(Patch(Scott(𝓓))) ≃ Spectral-Point(Scott(𝓓))
```

\begin{code}

module points-of-patch-are-spectral-points
        (𝓓  : DCPO {𝓤 ⁺} {𝓤})
        (hl : has-least (underlying-order 𝓓))
        (sd : is-scott-domain 𝓓 holds)
        (dc : decidability-condition 𝓓)
       where

 zd : zero-dimensionalᴰ {𝓤 ⁺} (𝒪 (𝟏Loc pe))
 zd = 𝟏-zero-dimensionalᴰ pe

 open SpectralScottLocaleConstruction₂ 𝓓 ua hl sd dc pe renaming (σ⦅𝓓⦆ to Scott⦅𝓓⦆)
 open Notion-Of-Spectral-Point
 open SmallPatchConstruction Scott⦅𝓓⦆ scott-locale-spectralᴰ
 open Preliminaries
 open UniversalProperty Scott⦅𝓓⦆ (𝟏Loc pe) scott-locale-spectralᴰ zd 𝟎Frm-is-compact
 open ContinuousMaps
 open ClosedNucleus Scott⦅𝓓⦆ scott-locale-is-spectral
 open Epsilon Scott⦅𝓓⦆ scott-locale-spectralᴰ
 open PatchStoneᴰ Scott⦅𝓓⦆ scott-locale-spectralᴰ

\end{code}

We define an alias for `Patch(Scott(𝓓))`

\begin{code}

 Patch⦅Scott⦅𝓓⦆⦆ : Locale (𝓤 ⁺) 𝓤 𝓤
 Patch⦅Scott⦅𝓓⦆⦆ = SmallPatch

 Patch⦅Scott⦅𝓓⦆⦆-stoneᴰ : stoneᴰ Patch⦅Scott⦅𝓓⦆⦆
 Patch⦅Scott⦅𝓓⦆⦆-stoneᴰ = patchₛ-is-compact , patchₛ-zero-dimensionalᴰ

\end{code}

We now instantiate to the universal property of `Patch⦅Scott⦅𝓓⦆⦆` to points
`𝟏 → Scott⦅𝓓⦆`.

\begin{code}

 patch-ump : (𝓅 : 𝟏Loc pe ─c→ Scott⦅𝓓⦆)
           → is-spectral-map Scott⦅𝓓⦆ (𝟏Loc pe) 𝓅 holds
           → ∃! 𝒻⁻ ꞉ 𝟏Loc pe ─c→ Patch⦅Scott⦅𝓓⦆⦆ , ((U : ⟨ 𝒪 Scott⦅𝓓⦆ ⟩) → 𝓅 .pr₁ U  ＝ 𝒻⁻ .pr₁ ‘ U ’ )
 patch-ump = ump-of-patch
              Scott⦅𝓓⦆
              scott-locale-is-spectral
              scott-locale-has-small-𝒦
              (𝟏Loc pe)
              (𝟏-is-stone pe)

\end{code}

This universal property immediately gives us a map from the spectral points of
`Scott⦅𝓓⦆` into the spectral points of `Patch⦅Scott⦅𝓓⦆⦆`.

\begin{code}

 to-patch-point : Spectral-Point Scott⦅𝓓⦆ → Spectral-Point Patch⦅Scott⦅𝓓⦆⦆
 to-patch-point ℱ = to-spectral-point Patch⦅Scott⦅𝓓⦆⦆ (𝓅 , †)
  where
   open Spectral-Point ℱ renaming (point to F; point-preserves-compactness to 𝕤)
   open continuous-maps-of-stone-locales (𝟏Loc pe) Patch⦅Scott⦅𝓓⦆⦆

   𝓅 : 𝟏Loc pe ─c→ Patch⦅Scott⦅𝓓⦆⦆
   𝓅 = ∃!-witness (patch-ump F 𝕤)

   † : is-spectral-map Patch⦅Scott⦅𝓓⦆⦆ (𝟏Loc pe) 𝓅 holds
   † = continuous-maps-between-stone-locales-are-spectral
        (𝟏-stoneᴰ pe)
        Patch⦅Scott⦅𝓓⦆⦆-stoneᴰ
        𝓅

\end{code}

The proof below should be placed in a more appropriate place.

\begin{code}

 ϵ-is-a-spectral-map : is-spectral-map Scott⦅𝓓⦆ Patch⦅Scott⦅𝓓⦆⦆ ϵ holds
 ϵ-is-a-spectral-map =
  perfect-maps-are-spectral
   Patch⦅Scott⦅𝓓⦆⦆
   Scott⦅𝓓⦆
   ∣ spectralᴰ-implies-basisᴰ Scott⦅𝓓⦆ scott-locale-spectralᴰ ∣
   ϵ
   ϵ-is-a-perfect-map

\end{code}

We now define the inverse of `to-patch-point`: given a spectral point `𝟏 →
Patch⦅Scott⦅𝓓⦆⦆`, we can compose this with `ϵ : Patch⦅Scott⦅𝓓⦆⦆ → Scott⦅𝓓⦆` to
obtain a map `𝟏 → Scott⦅𝓓⦆`. We call this map `to-scott-point`.

\begin{code}

 to-scott-point : Spectral-Point Patch⦅Scott⦅𝓓⦆⦆ → Spectral-Point Scott⦅𝓓⦆
 to-scott-point 𝓅 = to-spectral-point Scott⦅𝓓⦆ (𝓅₀ , 𝕤)
  where
   open Spectral-Point 𝓅 renaming (point to 𝓅⋆)

   𝓅₀ : 𝟏Loc pe ─c→ Scott⦅𝓓⦆
   𝓅₀ = cont-comp (𝟏Loc pe) Patch⦅Scott⦅𝓓⦆⦆ Scott⦅𝓓⦆ ϵ 𝓅⋆

   𝕤 : is-spectral-map Scott⦅𝓓⦆ (𝟏Loc pe) 𝓅₀ holds
   𝕤 K κ = point-preserves-compactness ‘ K ’ (ϵ-is-a-spectral-map K κ)

\end{code}

We now proceed to show these form a section-retraction pair.

\begin{code}

 to-scott-point-cancels-to-patch-point : to-scott-point ∘ to-patch-point ∼ id
 to-scott-point-cancels-to-patch-point 𝓅 =
  to-spectral-point-＝ Scott⦅𝓓⦆ (to-scott-point (to-patch-point 𝓅)) 𝓅 †
   where
    † : {!!} ＝ {!!}
    † = {!!}

\end{code}

\begin{code}

 to-patch-point-qinv : qinv to-patch-point
 to-patch-point-qinv = to-scott-point , † , ‡
  where
   open ContinuousMaps
   open ContinuousMapNotation (𝟏Loc pe) Patch⦅Scott⦅𝓓⦆⦆

   † : to-scott-point ∘ to-patch-point ∼ id
   † ℱ = to-spectral-point-＝ Scott⦅𝓓⦆ (to-scott-point (to-patch-point ℱ)) ℱ ♢
    where
     open Spectral-Point using (point; point-fn; point-preserves-compactness)
     open Spectral-Point ℱ using () renaming (point-fn to F)

     𝕤 : is-spectral-map Scott⦅𝓓⦆ (𝟏Loc pe) (point ℱ) holds
     𝕤 K κ = point-preserves-compactness ℱ K κ

     γ : (U : ⟨ 𝒪 Scott⦅𝓓⦆ ⟩)
       → point-fn (to-scott-point (to-patch-point ℱ)) U ＝ F U
     γ U = pr₂ (description (patch-ump (point ℱ) 𝕤)) U ⁻¹

     ♢ : point-fn (to-scott-point (to-patch-point ℱ)) ＝ F
     ♢ = dfunext fe γ

   ‡ : to-patch-point ∘ to-scott-point ∼ id
   ‡ 𝓅 = to-spectral-point-＝'
          Patch⦅Scott⦅𝓓⦆⦆
          (to-patch-point (to-scott-point 𝓅))
          𝓅
          (γ ⁻¹)
    where
     open Spectral-Point 𝓅 renaming (point-fn to p⋆; point to 𝓅⋆)
     open FrameHomomorphismProperties (𝒪 (𝟏Loc pe)) (𝒪 Patch⦅Scott⦅𝓓⦆⦆)

     𝓅₀ : 𝟏Loc pe ─c→ Scott⦅𝓓⦆
     𝓅₀ = cont-comp (𝟏Loc pe) Patch⦅Scott⦅𝓓⦆⦆ Scott⦅𝓓⦆ ϵ 𝓅⋆

     p₀ = pr₁ 𝓅₀

     𝕤 : is-spectral-map Scott⦅𝓓⦆ (𝟏Loc pe) 𝓅₀ holds
     𝕤 K κ = point-preserves-compactness ‘ K ’ (ϵ-is-a-spectral-map K κ)

     υ : ∃! 𝓅₀⁻ ꞉ 𝟏Loc pe ─c→ Patch⦅Scott⦅𝓓⦆⦆ , ((U : ⟨ 𝒪 Scott⦅𝓓⦆ ⟩) → p₀ U  ＝ 𝓅₀⁻ ⋆∙ ‘ U ’ )
     υ = patch-ump 𝓅₀ 𝕤

     𝓅₀⁻ : 𝟏Loc pe ─c→ Patch⦅Scott⦅𝓓⦆⦆
     𝓅₀⁻ = ∃!-witness υ

     foo : (U : ⟨ 𝒪 Scott⦅𝓓⦆ ⟩) → p₀ U ＝ p⋆ ‘ U ’
     foo U = refl

     γ : 𝓅⋆ ＝ 𝓅₀⁻
     γ = pr₁ (from-Σ-＝ (∃!-uniqueness υ 𝓅⋆ foo)) ⁻¹

\end{code}
