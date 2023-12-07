\begin{code}

{-# OPTIONS --safe --without-K #-}

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

open import Locales.Frame pt fe hiding (𝟚)
open import DomainTheory.Lifting.LiftingSet pt fe 𝓤 pe
open import DomainTheory.Lifting.LiftingSetAlgebraic pt pe fe 𝓤
open import DomainTheory.Basics.Dcpo    pt fe 𝓤 hiding (⟨_⟩)
open import DomainTheory.Basics.Pointed pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓤
open import Slice.Family

open import UF.SubtypeClassifier
open import UF.Subsingletons-Properties
open import UF.DiscreteAndSeparated
open import DomainTheory.Basics.Miscelanea pt fe 𝓤

\end{code}

We first define the Sierpinski domain.

\begin{code}

𝕊𝓓⁺ : DCPO {𝓤 ⁺ } {𝓤 ⁺}
𝕊𝓓⁺ = 𝓛-DCPO {X = 𝟙 {𝓤}} 𝟙-is-set

𝕊-is-locally-small : is-locally-small 𝕊𝓓⁺
𝕊-is-locally-small = 𝓛-is-locally-small {X = 𝟙 {𝓤}} 𝟙-is-set

𝕊𝓓⁺-has-specified-small-compact-basis : has-specified-small-compact-basis 𝕊𝓓⁺
𝕊𝓓⁺-has-specified-small-compact-basis =
 𝓛-has-specified-small-compact-basis 𝟙-is-set

𝕊𝓓⁺-is-algebraic : is-algebraic-dcpo (𝓛-DCPO {X = 𝟙 {𝓤}} 𝟙-is-set)
𝕊𝓓⁺-is-algebraic = 𝓛-is-algebraic-dcpo 𝟙-is-set

𝕊𝓓 : DCPO {𝓤 ⁺} {𝓤}
𝕊𝓓 = 𝓛-DCPO⁻ {X = 𝟙 {𝓤}} 𝟙-is-set

𝕊𝓓⊥ : DCPO⊥ {𝓤 ⁺} {𝓤}
𝕊𝓓⊥ = 𝕊𝓓 , ((𝟘 , (λ ()) , 𝟘-is-prop) , λ _ → (λ ()) , λ ())

\end{code}

We then define the Sierpinski locale as the Scott locale of the Sierpinski
domain.

\begin{code}

{--
open import Locales.ScottLocale.Definition pt fe 𝓤

open DefnOfScottLocale 𝕊-dcpo 𝓤 pe
open Locale
open import Lifting.Lifting (𝓤 ⁺)

𝕊 : Locale (𝓤 ⁺) (𝓤 ⁺) 𝓤
𝕊 = ScottLocale

⊤𝕊 : ⟨ 𝒪 𝕊 ⟩
⊤𝕊 = ⊤ₛ
--}

\end{code}
