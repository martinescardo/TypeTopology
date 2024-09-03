\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt
open import UF.Logic
open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.Subsingletons

module Locales.Sierpinski
        (𝓤  : Universe)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext) where

open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤
open import DomainTheory.Basics.Dcpo pt fe 𝓤 hiding (⟨_⟩)
open import DomainTheory.Basics.Pointed pt fe 𝓤
open import DomainTheory.Lifting.LiftingSet pt fe
open import DomainTheory.Lifting.LiftingSetAlgebraic pt pe fe
open import Locales.Frame pt fe hiding (𝟚)
open import Slice.Family

open import UF.SubtypeClassifier
open import UF.Subsingletons-Properties

\end{code}

We first define the Sierpinski domain.

\begin{code}

𝕊-dcpo⁻ : DCPO {𝓤 ⁺} {𝓤 ⁺}
𝕊-dcpo⁻ = 𝓛-DCPO 𝓤 pe (props-are-sets {X = 𝟙 {𝓤}} 𝟙-is-prop)

𝕊-dcpo : DCPO⊥ {𝓤 ⁺} {𝓤 ⁺}
𝕊-dcpo = 𝓛-DCPO⊥ 𝓤 pe (props-are-sets {X = 𝟙 {𝓤}} 𝟙-is-prop)

\end{code}

We then define the Sierpinski locale as the Scott locale of the Sierpinski
domain.

\begin{code}

open import Locales.ScottLocale.Definition pt fe 𝓤

open DefnOfScottLocale (𝕊-dcpo ⁻) 𝓤 pe
open Locale
open import Lifting.Construction (𝓤 ⁺)

𝕊 : Locale (𝓤 ⁺) (𝓤 ⁺) 𝓤
𝕊 = ScottLocale

⊤𝕊 : ⟨ 𝒪 𝕊 ⟩
⊤𝕊 = ⊤ₛ

𝕊𝓓-is-algebraic : is-algebraic-dcpo 𝕊-dcpo⁻
𝕊𝓓-is-algebraic = 𝓛-is-algebraic-dcpo 𝓤 (props-are-sets {X = 𝟙 {𝓤}} 𝟙-is-prop)

\end{code}
