---
title:        Properties of the patch locale of the Sierpiński locale
author:       Ayberk Tosun
date-started: 2024-03-11
---

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt
open import UF.Logic
open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Size

module Locales.Sierpinski.Patch-Properties
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
open import Lifting.Lifting 𝓤
open import Lifting.Miscelanea-PropExt-FunExt 𝓤 pe fe
open import Lifting.UnivalentPrecategory 𝓤 (𝟙 {𝓤})
open import Locales.Frame pt fe hiding (𝟚; is-directed)
open import Locales.InitialFrame pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.Sierpinski.Definition 𝓤 pe pt fe sr
open import Locales.Sierpinski.Properties 𝓤 pe pt fe sr
open import Locales.Sierpinski.UniversalProperty 𝓤 fe pe pt sr
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import Locales.DiscreteLocale.Two fe pe pt
open import Locales.Stone pt fe sr
open import Slice.Family
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Subsingletons-Properties
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open Locale

open PropositionalTruncation pt

\end{code}

\begin{code}

module _ (S : Locale (𝓤 ⁺) 𝓤 𝓤)
         (truth : ⟨ 𝒪 S ⟩)
         (ump : has-the-universal-property-of-sierpinski S truth) where

\end{code}

\begin{code}

 𝔠₀ : 𝟚-loc 𝓤 ─c→ S
 𝔠₀ = pr₁ (center (ump (𝟚-loc 𝓤) true₂))

\end{code}
