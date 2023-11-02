\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.Logic
open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.Subsingletons

module Locales.Sierpinski
        (𝓤  : Universe)
        (pe : propext 𝓤)
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext) where

open import Locales.Frame pt fe hiding (𝟚)
open import DomainTheory.Lifting.LiftingSet pt fe
open import DomainTheory.Basics.Pointed pt fe 𝓤
open import Slice.Family

open import UF.SubtypeClassifier
open import UF.Subsingletons-Properties

\end{code}

We first define the Sierpinski domain.

\begin{code}

𝕊-dcpo : DCPO⊥
𝕊-dcpo = 𝓛-DCPO⊥ 𝓤 pe (props-are-sets {X = 𝟙 {𝓤 ⁺}} 𝟙-is-prop)

\end{code}

We then define the Sierpinski locale as the Scott locale of the Sierpinski
domain.

\begin{code}

open import Locales.ScottLocale.Definition pt fe 𝓤

open DefnOfScottLocale (𝕊-dcpo ⁻) 𝓤 pe
open Locale
open import Lifting.Lifting (𝓤 ⁺)

𝕊 : Locale (𝓤 ⁺) (𝓤 ⁺) 𝓤
𝕊 = ScottLocale

⊤𝕊 : ⟨ 𝒪 𝕊 ⟩
⊤𝕊 = ⊤ₛ

\end{code}
