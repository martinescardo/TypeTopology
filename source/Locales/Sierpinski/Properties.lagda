---
title:          Some properties of the Sierpiński locale
author:         Ayberk Tosun
date-completed: 2024-02-12
---

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt
open import UF.Logic
open import MLTT.Spartan hiding (𝟚; ₀; ₁)
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
open import DomainTheory.Topology.ScottTopology pt fe 𝓤
open import Lifting.Construction 𝓤
open import Lifting.Miscelanea-PropExt-FunExt 𝓤 pe fe
open import Lifting.UnivalentPrecategory 𝓤 (𝟙 {𝓤})
open import Locales.Frame pt fe hiding (is-directed)
open import Locales.InitialFrame pt fe
open import Locales.ScottLocale.Definition pt fe 𝓤
open import Locales.ScottLocale.Properties pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤
open import Locales.Sierpinski.Definition 𝓤 pe pt fe sr
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import Locales.Stone pt fe sr
open import MLTT.List hiding ([_])
open import Slice.Family
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier

open AllCombinators pt fe
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

From all these, we obtain the fact that `𝕊` is a spectral locale, which we call
`𝕊-is-spectral` below.

\begin{code}

𝕊𝓓-has-least : has-least (underlying-order 𝕊𝓓)
𝕊𝓓-has-least = (⊥∙ 𝕊𝓓⊥) , ⊥-is-least 𝕊𝓓⊥

open ScottLocaleConstruction 𝕊𝓓 hscb pe
open SpectralScottLocaleConstruction 𝕊𝓓 𝕊𝓓-has-least hscb 𝕊𝓓-satisfies-dc 𝕊𝓓-bounded-complete pe
open ScottLocaleProperties 𝕊𝓓 𝕊𝓓-has-least hscb pe
open DefnOfScottLocale 𝕊𝓓 𝓤 pe using (𝒪ₛ-equality; _⊆ₛ_)

ℬ𝕊 : Fam 𝓤 ⟨ 𝒪 𝕊 ⟩
ℬ𝕊 = List (𝟚 𝓤) , 𝜸

principal-filter-on-₁-is-truth : ↑ᵏ[ ₁ ] ＝ truth
principal-filter-on-₁-is-truth = ≤-is-antisymmetric (poset-of (𝒪 𝕊)) † ‡
 where
  †₀ : (↑ᵏ[ ₁ ] ⊆ₛ truth) holds
  †₀ (P , f , φ) (p , _) = p ⋆

  † : (↑ᵏ[ ₁ ] ⊆ₖ truth) holds
  † = ⊆ₛ-implies-⊆ₖ ↑ᵏ[ ₁ ] truth †₀

  ‡₀ : (truth ⊆ₛ ↑ᵏ[ ₁ ]) holds
  ‡₀ (P , f , φ) p = (λ x → p) , λ { _ → 𝟙-is-prop ⋆ ⋆ }

  ‡ : (truth ⊆ₖ ↑ᵏ[ ₁ ]) holds
  ‡ = ⊆ₛ-implies-⊆ₖ truth ↑ᵏ[ ₁ ] ‡₀

𝕊-is-spectralᴰ : spectralᴰ 𝕊
𝕊-is-spectralᴰ = σᴰ

open import Locales.PatchLocale pt fe sr

𝕊-is-spectral : is-spectral 𝕊 holds
𝕊-is-spectral = spectralᴰ-gives-spectrality 𝕊 σᴰ

𝕊-has-small-𝒦 : has-small-𝒦 𝕊
𝕊-has-small-𝒦 = spectralᴰ-implies-small-𝒦 𝕊 σᴰ

\end{code}

Added on 2024-03-09.

A basic open of the Sierpiński locale is either `𝟏`, `truth`, or `𝟎`. In fact,
because the basic open coincide with the compact opens in spectral locales, a
corollary of this is that these three elements form a basis for Sierpiński.

\begin{code}

basis-trichotomy : (bs : List (𝟚 𝓤))
                 → (𝜸 bs ＝ 𝟏[ 𝒪 𝕊 ]) + (𝜸 bs ＝ truth) + (𝜸 bs ＝ 𝟎[ 𝒪 𝕊 ])
basis-trichotomy []       = inr (inr p)
                             where
                              p : 𝜸 [] ＝ 𝟎[ 𝒪 𝕊 ]
                              p = 𝜸 []     ＝⟨ 𝜸-equal-to-𝜸₁ [] ⟩
                                  𝜸₁ []    ＝⟨ refl             ⟩
                                  𝟎[ 𝒪 𝕊 ] ∎
basis-trichotomy (₀ ∷ bs) = inl p
                             where
                              Ⅰ = 𝜸-equal-to-𝜸₁ (₀ ∷ bs)
                              Ⅱ = ap (λ - → - ∨[ 𝒪 𝕊 ] 𝜸₁ bs) ↑⊥-is-top
                              Ⅲ = 𝟏-left-annihilator-for-∨ (𝒪 𝕊) (𝜸₁ bs)

                              p : 𝜸 (₀ ∷ bs) ＝ 𝟏[ 𝒪 𝕊 ]
                              p = 𝜸 (₀ ∷ bs)               ＝⟨ Ⅰ    ⟩
                                  𝜸₁ (₀ ∷ bs)              ＝⟨ refl ⟩
                                  ↑ᵏ[ ₀ ] ∨[ 𝒪 𝕊 ] 𝜸₁ bs   ＝⟨ Ⅱ    ⟩
                                  𝟏[ 𝒪 𝕊 ] ∨[ 𝒪 𝕊 ] 𝜸₁ bs  ＝⟨ Ⅲ    ⟩
                                  𝟏[ 𝒪 𝕊 ]                 ∎
basis-trichotomy (₁ ∷ bs) = cases₃ case₁ case₂ case₃ IH
 where
  IH : (𝜸 bs ＝ 𝟏[ 𝒪 𝕊 ]) + (𝜸 bs ＝ truth) + (𝜸 bs ＝ 𝟎[ 𝒪 𝕊 ])
  IH = basis-trichotomy bs

  case₁ : 𝜸 bs ＝ 𝟏[ 𝒪 𝕊 ]
        → (𝜸 (₁ ∷ bs) ＝ 𝟏[ 𝒪 𝕊 ]) + (𝜸 (₁ ∷ bs) ＝ truth) + (𝜸 (₁ ∷ bs) ＝ 𝟎[ 𝒪 𝕊 ])
  case₁ q = inl r
   where
    Ⅱ = ap
         (λ - → ↑ᵏ[ ₁ ] ∨[ 𝒪 𝕊 ] -)
         (𝜸₁ bs ＝⟨ 𝜸-equal-to-𝜸₁ bs ⁻¹ ⟩ 𝜸 bs ＝⟨ q ⟩ 𝟏[ 𝒪 𝕊 ] ∎ )
    Ⅲ = 𝟏-right-annihilator-for-∨ (𝒪 𝕊) ↑ᵏ[ ₁ ]

    r : 𝜸 (₁ ∷ bs) ＝ 𝟏[ 𝒪 𝕊 ]
    r = 𝜸 (₁ ∷ bs)                ＝⟨ 𝜸-equal-to-𝜸₁ (₁ ∷ bs) ⟩
        𝜸₁ (₁ ∷ bs)               ＝⟨ refl ⟩
        ↑ᵏ[ ₁ ] ∨[ 𝒪 𝕊 ] 𝜸₁ bs    ＝⟨ Ⅱ ⟩
        ↑ᵏ[ ₁ ] ∨[ 𝒪 𝕊 ] 𝟏[ 𝒪 𝕊 ] ＝⟨ Ⅲ ⟩
        𝟏[ 𝒪 𝕊 ]                  ∎

  case₂ : 𝜸 bs ＝ truth
        → (𝜸 (₁ ∷ bs) ＝ 𝟏[ 𝒪 𝕊 ]) + (𝜸 (₁ ∷ bs) ＝ truth) + (𝜸 (₁ ∷ bs) ＝ 𝟎[ 𝒪 𝕊 ])
  case₂ q = inr (inl r)
   where
    Ⅱ = ap (λ - → - ∨[ 𝒪 𝕊 ] 𝜸₁ bs) principal-filter-on-₁-is-truth
    Ⅲ = ap (λ - → truth ∨[ 𝒪 𝕊 ] -) (𝜸-equal-to-𝜸₁ bs ⁻¹)
    Ⅳ = ap (λ - → truth ∨[ 𝒪 𝕊 ] -) q
    Ⅴ = ∨[ 𝒪 𝕊 ]-is-idempotent truth ⁻¹

    r : 𝜸 (₁ ∷ bs) ＝ truth
    r = 𝜸 (₁ ∷ bs)               ＝⟨ 𝜸-equal-to-𝜸₁ (₁ ∷ bs) ⟩
        𝜸₁ (₁ ∷ bs)              ＝⟨ refl                   ⟩
        ↑ᵏ[ ₁ ] ∨[ 𝒪 𝕊 ] 𝜸₁ bs   ＝⟨ Ⅱ                      ⟩
        truth ∨[ 𝒪 𝕊 ] 𝜸₁ bs     ＝⟨ Ⅲ                      ⟩
        truth ∨[ 𝒪 𝕊 ] 𝜸 bs      ＝⟨ Ⅳ                      ⟩
        truth ∨[ 𝒪 𝕊 ] truth     ＝⟨ Ⅴ                      ⟩
        truth                    ∎

  case₃ : 𝜸 bs ＝ 𝟎[ 𝒪 𝕊 ]
        → (𝜸 (₁ ∷ bs) ＝ 𝟏[ 𝒪 𝕊 ]) + (𝜸 (₁ ∷ bs) ＝ truth) + (𝜸 (₁ ∷ bs) ＝ 𝟎[ 𝒪 𝕊 ])
  case₃ q = inr (inl r)
   where
    Ⅰ = 𝜸-equal-to-𝜸₁ (₁ ∷ bs)
    Ⅱ = ap
         (λ - → ↑ᵏ[ ₁ ] ∨[ 𝒪 𝕊 ] -)
         (𝜸₁ bs ＝⟨ 𝜸-equal-to-𝜸₁ bs ⁻¹ ⟩ 𝜸 bs ＝⟨ q ⟩ 𝟎[ 𝒪 𝕊 ] ∎)
    Ⅲ = 𝟎-left-unit-of-∨ (𝒪 𝕊) ↑ᵏ[ ₁ ]
    Ⅳ = principal-filter-on-₁-is-truth

    r : 𝜸 (₁ ∷ bs) ＝ truth
    r = 𝜸 (₁ ∷ bs)                ＝⟨ Ⅰ     ⟩
        𝜸₁ (₁ ∷ bs)               ＝⟨ refl  ⟩
        ↑ᵏ[ ₁ ] ∨[ 𝒪 𝕊 ] 𝜸₁ bs    ＝⟨ Ⅱ     ⟩
        ↑ᵏ[ ₁ ] ∨[ 𝒪 𝕊 ] 𝟎[ 𝒪 𝕊 ] ＝⟨ Ⅲ     ⟩
        ↑ᵏ[ ₁ ]                   ＝⟨ Ⅳ     ⟩
        truth                     ∎

\end{code}

Added on 2024-03-11.

\begin{code}

open DefnOfScottTopology 𝕊𝓓 𝓤

contains-⊥ₛ-implies-contains-⊤ₛ : (𝔘 : ⟨ 𝒪 𝕊 ⟩) → (⊥ₛ ∈ₛ 𝔘 ⇒ ⊤ₛ ∈ₛ 𝔘) holds
contains-⊥ₛ-implies-contains-⊤ₛ 𝔘 μ = transport (λ - → (⊤ₛ ∈ₛ -) holds) (q ⁻¹) ⋆
 where
  open 𝒪ₛᴿ

  q : 𝔘 ＝ 𝟏[ 𝒪 𝕊 ]
  q = contains-bottom-implies-is-𝟏 𝔘 μ

holds-gives-equal-⊤ₛ : (P : ⟨ 𝕊𝓓 ⟩∙) → (P ∈ₛ truth) holds → P ＝ ⊤ₛ
holds-gives-equal-⊤ₛ (P , f , φ) p =
 to-subtype-＝
  (λ Q → ×-is-prop (Π-is-prop fe (λ _ → 𝟙-is-prop)) (being-prop-is-prop fe))
  (holds-gives-equal-𝟙 pe P φ p)

contains-⊤ₛ-implies-above-truth : (𝔘 : ⟨ 𝒪 𝕊 ⟩)
                                → (⊤ₛ ∈ₛ 𝔘) holds
                                → (truth ≤[ poset-of (𝒪 𝕊) ] 𝔘) holds
contains-⊤ₛ-implies-above-truth 𝔘 μₜ = ⊆ₛ-implies-⊆ₖ truth 𝔘 †
 where
  † : (truth ⊆ₛ 𝔘) holds
  † P μₚ = transport (λ - → (- ∈ₛ 𝔘) holds) (holds-gives-equal-⊤ₛ P μₚ ⁻¹) μₜ

\end{code}

Added on 2024-03-11.

If a Scott open `𝔘` is above truth, then it obviously contains the true
proposition `⊤ₛ`.

\begin{code}

above-truth-implies-contains-⊤ₛ : (𝔘 : ⟨ 𝒪 𝕊 ⟩)
                                → (truth ≤[ poset-of (𝒪 𝕊) ] 𝔘) holds
                                → (⊤ₛ ∈ₛ 𝔘) holds
above-truth-implies-contains-⊤ₛ 𝔘 p = ⊆ₖ-implies-⊆ₛ truth 𝔘 p ⊤ₛ ⋆

\end{code}
