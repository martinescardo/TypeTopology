---
title:          Some properties of the Sierpiński locale
author:         Ayberk Tosun
date-completed: 2024-02-12
---

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt
open import UF.Logic
open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Size

module Locales.Sierpinski.Properties
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
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
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

We show that `𝕊𝓓` is a Scott domain. We have already shown that it is an
algebraic lattice, so it remains to show that it is bounded complete.

\begin{code}

open import DomainTheory.BasesAndContinuity.ScottDomain pt fe 𝓤

open DefinitionOfBoundedCompleteness

⊑₀-implies-⊑ : (x y : ⟨ 𝕊𝓓 ⟩∙)
             → x ⊑⟨ 𝕊𝓓 ⟩ y
             → (to-Ω x ≤[ poset-of (𝟎-𝔽𝕣𝕞 pe) ] to-Ω y) holds
⊑₀-implies-⊑ _ _ (g , q) p = g p

⊑-implies-⊑₀ : (x y : ⟨ 𝕊𝓓 ⟩∙)
             → (to-Ω x ≤[ poset-of (𝟎-𝔽𝕣𝕞 pe) ] to-Ω y) holds
             → x ⊑⟨ 𝕊𝓓 ⟩ y
⊑-implies-⊑₀ (P , f , h) (P′ , f′ , h′) p = p , (λ _ → 𝟙-is-prop ⋆ ⋆)

𝕊𝓓-bounded-complete : bounded-complete 𝕊𝓓 holds
𝕊𝓓-bounded-complete S _ = sup , φ
 where
  S₀ : Fam 𝓤 (Ω 𝓤)
  S₀ = ⁅ to-Ω P ∣ P ε S ⁆

  sup₀ : Ω 𝓤
  sup₀ = ⋁[ (𝟎-𝔽𝕣𝕞 pe) ] S₀

  sup : ⟨ 𝕊𝓓 ⟩∙
  sup = sup₀ holds , (λ _ → ⋆) , ∃-is-prop

  υ : is-upperbound (underlying-order 𝕊𝓓) sup (S [_])
  υ i = † , ‡
   where
    † : is-defined (S [ i ]) → is-defined sup
    † p = ∣ i , p ∣

    ‡ : value (S [ i ]) ∼ (λ x₁ → value sup († x₁))
    ‡ _ = 𝟙-is-prop ⋆ ⋆

  ϑ : is-lowerbound-of-upperbounds (underlying-order 𝕊𝓓) sup (S [_])
  ϑ (P , f , h) q = ⊑-implies-⊑₀ sup (P , f , h) (⋁[ 𝟎-𝔽𝕣𝕞 pe ]-least S₀ ((P , h) , (λ i → pr₁ (q i))))

  φ : is-sup (underlying-order 𝕊𝓓) sup (S [_])
  φ = υ , ϑ

\end{code}

Finally, we show that `𝕊𝓓` trivially satisfies the decidability condition that
we assume in the proof that Scott locales of Scott domains are spectral.

\begin{code}

open import Locales.ScottLocale.ScottLocalesOfScottDomains pt fe sr 𝓤

𝕊𝓓-satisfies-dc : decidability-condition 𝕊𝓓
𝕊𝓓-satisfies-dc 𝒫₀@(P₀ , h₀ , f₀) 𝒫₁@(P₁ , h₁ , f₁) κc κd =
 inl ∣ up , ‡ ∣
  where
   up : ⟨ 𝕊𝓓 ⟩∙
   up = to-𝕊𝓓 (to-Ω 𝒫₀ ∨[ 𝟎-𝔽𝕣𝕞 pe ] to-Ω 𝒫₁)

   open Joins {A = ⟨ 𝕊𝓓 ⟩∙} (λ x y → (x ⊑⟨ 𝕊𝓓 ⟩ y) , prop-valuedness 𝕊𝓓 x y)

   ‡ : (up is-an-upper-bound-of (binary-family 𝓤 𝒫₀ 𝒫₁)) holds
   ‡ (inl ⋆) = (λ p → ∣ inl ⋆ , p ∣) , λ _ → 𝟙-is-prop ⋆ ⋆
   ‡ (inr ⋆) = (λ p → ∣ inr ⋆ , p ∣) , λ _ → 𝟙-is-prop ⋆ ⋆

\end{code}

From all these, we obtain the fact that `𝕊` is a spectral locale.

\begin{code}

𝕊𝓓-has-least : has-least (underlying-order 𝕊𝓓)
𝕊𝓓-has-least = (⊥∙ 𝕊𝓓⊥) , ⊥-is-least 𝕊𝓓⊥

open SpectralScottLocaleConstruction 𝕊𝓓 𝕊𝓓-has-least hscb 𝕊𝓓-satisfies-dc 𝕊𝓓-bounded-complete pe

𝕊-is-spectralᴰ : spectralᴰ 𝕊
𝕊-is-spectralᴰ = σᴰ

open import Locales.PatchLocale pt fe sr

𝕊-is-spectral : is-spectral 𝕊 holds
𝕊-is-spectral = spectralᴰ-gives-spectrality 𝕊 σᴰ

𝕊-has-small-𝒦 : has-small-𝒦 𝕊
𝕊-has-small-𝒦 = spectralᴰ-implies-small-𝒦 𝕊 σᴰ

\end{code}
