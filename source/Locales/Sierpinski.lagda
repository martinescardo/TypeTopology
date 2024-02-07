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
open import Locales.Frame pt fe hiding (𝟚)
open import Slice.Family
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier

open PropositionalTruncation pt

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

𝟙-is-top : (x : ⟨ 𝕊𝓓 ⟩∙) → x ⊑⟨ 𝕊𝓓 ⟩ η ⋆
𝟙-is-top (P , q) = (λ _ → ⋆) , λ _ → refl

𝕊𝓓-is-compact : is-compact 𝕊𝓓 (η ⋆)
𝕊𝓓-is-compact I α δ⁻ p⁻ = ∥∥-rec ∃-is-prop † (ηs-are-compact 𝟙-is-set ⋆ I α δ p)
 where
  open is-locally-small 𝕊-is-locally-small

  δ : {!!}
  δ = {!!}

  p : η ⋆ ⊑⟨ 𝕊𝓓⁺ ⟩ (∐ (𝓛-DCPO 𝟙-is-set) δ)
  p = ⊑-to-⊑' ((λ x → {!!}) , λ x → {!!})

  † : {!!}
  † = {!!}

\end{code}

We then define the Sierpinski locale as the Scott locale of the Sierpinski
domain.

\begin{code}

open import Locales.ScottLocale.Definition pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤

hscb : has-specified-small-compact-basis 𝕊𝓓
hscb = (𝟙 {𝓤} + 𝟙 {𝓤}) , β , σ
 where
  β : 𝟙 + 𝟙 → ⟨ 𝕊𝓓 ⟩∙
  β (inl ⋆) = ⊥∙ (𝓛-DCPO⊥ 𝟙-is-set)
  β (inr ⋆) = 𝟙 {𝓤} , (λ { ⋆ → ⋆ }) , 𝟙-is-prop

  β-is-compact : (b : 𝟙 + 𝟙) → is-compact 𝕊𝓓 (β b)
  β-is-compact (inl ⋆) = ⊥-is-compact 𝕊𝓓⊥
  β-is-compact (inr ⋆) = {!!}

  β-is-upward-directed : (x : ⟨ 𝕊𝓓 ⟩∙)
                       → is-semidirected (underlying-order 𝕊𝓓) (↓-inclusion 𝕊𝓓 β x)
  β-is-upward-directed x (inl ⋆ , p) (z , q)  = let
                                                 u = (z , q)
                                                 r₁ = reflexivity 𝕊𝓓 (β (inl ⋆))
                                                 r₂ = reflexivity 𝕊𝓓 (β z)
                                                in
                                                 ∣ u , ⊥-is-least 𝕊𝓓⊥ (β z) , r₂ ∣
  β-is-upward-directed x (inr ⋆ , p₁) (z , q) = let
                                                 r₁ = reflexivity 𝕊𝓓 (β (inr ⋆))
                                                 r₂ = reflexivity 𝕊𝓓 (β (inr ⋆))
                                                in
                                                 ∣ (inr ⋆ , p₁) , r₁ , 𝟙-is-top (β z) ∣

  σ : is-small-compact-basis 𝕊𝓓 β
  σ = record
       { basis-is-compact = β-is-compact
       ; ⊑ᴮ-is-small = λ x b → (β b ⊑⟨ 𝕊𝓓 ⟩ x) , ≃-refl (β b ⊑⟨ 𝕊𝓓 ⟩ x)
       ; ↓ᴮ-is-directed = λ x → ∣ (inl ⋆) , ⊥-is-least 𝕊𝓓⊥ x ∣ , β-is-upward-directed x
       ; ↓ᴮ-is-sup = {!!}
       }

-- open ScottLocaleConstruction 𝕊𝓓

{--

open DefnOfScottLocale 𝕊-dcpo 𝓤 pe
open Locale
open import Lifting.Lifting (𝓤 ⁺)

𝕊 : Locale (𝓤 ⁺) (𝓤 ⁺) 𝓤
𝕊 = ScottLocale

⊤𝕊 : ⟨ 𝒪 𝕊 ⟩
⊤𝕊 = ⊤ₛ
--}

\end{code}
