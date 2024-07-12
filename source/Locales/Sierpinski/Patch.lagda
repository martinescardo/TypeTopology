---
title:          The patch locale of the Sierpiński locale
author:         Ayberk Tosun
date-completed: 2024-02-12
---

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons

module Locales.Sierpinski.Patch
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
open import Lifting.Construction 𝓤
open import Lifting.Miscelanea-PropExt-FunExt 𝓤 pe fe
open import Lifting.UnivalentPrecategory 𝓤 (𝟙 {𝓤})
open import Locales.Compactness pt fe
open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.Frame pt fe hiding (𝟚; is-directed)
open import Locales.HeytingImplication pt fe
open import Locales.InitialFrame pt fe
open import Locales.Sierpinski.Definition 𝓤 pe pt fe sr
open import Locales.Sierpinski.Properties 𝓤 pe pt fe sr
open import Locales.SmallBasis pt fe sr
open import Locales.Complements pt fe
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import Locales.Stone pt fe sr
open import MLTT.List hiding ([_])
open import Slice.Family
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Logic
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier

open ContinuousMaps
open FrameHomomorphismProperties
open FrameHomomorphisms
open Locale
open PropositionalTruncation pt

\end{code}

We conclude by constructing the patch of Sierpiński.

\begin{code}

open import Locales.ScottLocale.ScottLocalesOfScottDomains pt fe sr 𝓤

open SpectralScottLocaleConstruction 𝕊𝓓 𝕊𝓓-has-least hscb 𝕊𝓓-satisfies-dc 𝕊𝓓-bounded-complete pe

open import Locales.PatchLocale pt fe sr

open SmallPatchConstruction 𝕊 𝕊-is-spectralᴰ renaming (SmallPatch to Patch-𝕊)

patch-of-𝕊 : Locale (𝓤 ⁺) 𝓤 𝓤
patch-of-𝕊 = Patch-𝕊

\end{code}

The universal property of Patch then specializes to the following.

\begin{code}

open import Locales.UniversalPropertyOfPatch pt fe sr
open import Locales.PatchProperties pt fe sr

open ClosedNucleus 𝕊 𝕊-is-spectral
open ContinuousMaps
open PatchConstruction 𝕊 𝕊-is-spectral

ump-for-patch-of-𝕊 : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
                   → is-stone X holds
                   → (𝒻@(f , _) : X ─c→ 𝕊)
                   → is-spectral-map 𝕊 X 𝒻 holds
                   → ∃! 𝒻⁻@(f⁻ , _) ꞉ X ─c→ Patch-𝕊 ,
                      ((U : ⟨ 𝒪 𝕊 ⟩) → f U ＝ f⁻ ‘ U ’)
ump-for-patch-of-𝕊 = ump-of-patch 𝕊 𝕊-is-spectral 𝕊-has-small-𝒦

\end{code}

We show that there are exactly four compact opens in `Patch(𝕊)`.

The first one: the closed nucleus on the top element of `𝕊`.

\begin{code}

closed-𝟏 : ⟨ 𝒪 Patch-𝕊 ⟩
closed-𝟏 = ‘ 𝟏[ 𝒪 𝕊 ] ’

\end{code}

\begin{code}

closed-𝟏-is-top : closed-𝟏 ＝ 𝟏[ 𝒪 Patch-𝕊 ]
closed-𝟏-is-top = only-𝟏-is-above-𝟏 (𝒪 Patch-𝕊) closed-𝟏 †
 where
  † : (𝟏[ 𝒪 Patch-𝕊 ] ≤[ poset-of (𝒪 Patch-𝕊) ] closed-𝟏) holds
  † = ≼-implies-≼ᵏ 𝟏[ 𝒪 Patch-𝕊 ] closed-𝟏 (∨[ 𝒪 𝕊 ]-upper₁ 𝟏[ 𝒪 𝕊 ])

\end{code}

The second one: the closed nucleus on the bottom element of `𝕊`.

\begin{code}

closed-𝟎 : ⟨ 𝒪 Patch-𝕊 ⟩
closed-𝟎 = ‘ 𝟎[ 𝒪 𝕊 ] ’

open PatchStoneᴰ 𝕊 𝕊-is-spectralᴰ
open BasisOfPatch 𝕊 𝕊-is-spectralᴰ
open OpenNucleus 𝕊 𝕊-is-spectralᴰ 𝕊-has-small-𝒦

open-𝟏 : ⟨ 𝒪 Patch-𝕊 ⟩
open-𝟏 = ¬‘ 𝟏[ 𝒪 𝕊 ] , 𝕊-is-compact ’

\end{code}

This is the same thing as the bottom nucleus.

\begin{code}

closed-𝟎-is-bottom : closed-𝟎 ＝ 𝟎[ 𝒪 Patch-𝕊 ]
closed-𝟎-is-bottom =
 perfect-nuclei-eq closed-𝟎 𝟎[ 𝒪 Patch-𝕊 ] (dfunext fe †)
 where
  † : closed-𝟎 $_ ∼ 𝟎[ 𝒪 Patch-𝕊 ] $_
  † U = 𝟎[ 𝒪 𝕊 ] ∨[ 𝒪 𝕊 ] U    ＝⟨ 𝟎-right-unit-of-∨ (𝒪 𝕊) U ⟩
        U                      ＝⟨ 𝟎-is-id U ⁻¹ ⟩
        𝟎[ 𝒪 Patch-𝕊 ] .pr₁ U  ∎

𝕊-has-basis : has-basis (𝒪 𝕊) holds
𝕊-has-basis = ∣ spectralᴰ-implies-basisᴰ 𝕊 σᴰ ∣

open HeytingImplicationConstruction 𝕊 𝕊-has-basis

open-𝟏-is-bottom : open-𝟏 ＝ 𝟎[ 𝒪 Patch-𝕊 ]
open-𝟏-is-bottom = perfect-nuclei-eq open-𝟏 𝟎[ 𝒪 Patch-𝕊 ] (dfunext fe γ)
 where
  open PosetReasoning (poset-of (𝒪 𝕊)) renaming (_■ to QED)

  γ : (U : ⟨ 𝒪 𝕊 ⟩) → open-𝟏 .pr₁ U ＝ 𝟎[ 𝒪 Patch-𝕊 ] .pr₁ U
  γ U = open-𝟏 .pr₁ U         ＝⟨ 𝟏-==>-law U ⁻¹ ⟩
        U                     ＝⟨ 𝟎-is-id U ⁻¹ ⟩
        𝟎[ 𝒪 Patch-𝕊 ] .pr₁ U ∎

open-𝟎 : ⟨ 𝒪 Patch-𝕊 ⟩
open-𝟎 = ¬‘ 𝟎[ 𝒪 𝕊 ] , 𝟎-is-compact 𝕊 ’

open-𝟎-is-top : open-𝟎 ＝ 𝟏[ 𝒪 Patch-𝕊 ]
open-𝟎-is-top = perfect-nuclei-eq open-𝟎 𝟏[ 𝒪 Patch-𝕊 ] (dfunext fe †)
 where
  † : open-𝟎 .pr₁ ∼ 𝟏[ 𝒪 Patch-𝕊 ] .pr₁
  † U = ex-falso-quodlibet-eq U ⁻¹

\end{code}

The third one: the closed nucleus on the singleton set `{ ⊤ }`.

\begin{code}

closed-truth : ⟨ 𝒪 Patch-𝕊 ⟩
closed-truth = ‘ truth ’

\end{code}

The fourth one: the _open_ nucleus on the singleton `{ ⊤ }`.

\begin{code}

truthₖ : 𝒦 𝕊
truthₖ = truth , truth-is-compact

open-truth : ⟨ 𝒪 Patch-𝕊 ⟩
open-truth = ¬‘ truthₖ ’

open PatchComplementation 𝕊 σᴰ

important-lemma : open-truth ∨[ 𝒪 Patch-𝕊 ] closed-truth ＝ 𝟏[ 𝒪 Patch-𝕊 ]
important-lemma = pr₂ (closed-complements-open truth truth-is-compact)

\end{code}

We now write down a type family expressing that a given open is equal to one
of these four opens.

\begin{code}

equal-to-one-of-the-four-compact-opensₚ : (U : ⟨ 𝒪 Patch-𝕊 ⟩ ) → 𝓤 ⁺  ̇
equal-to-one-of-the-four-compact-opensₚ U =
 (U ＝ closed-𝟎) + (U ＝ closed-truth) + (U ＝ open-truth) + (U ＝ closed-𝟏)

case-lemma₁ : (𝒿 𝓀 : ⟨ 𝒪 Patch-𝕊 ⟩)
            → 𝓀 ＝ closed-𝟏
            → equal-to-one-of-the-four-compact-opensₚ (𝒿 ∨[ 𝒪 Patch-𝕊 ] 𝓀)
case-lemma₁ 𝒿 𝓀 p = inr (inr (inr †))
 where
  Ⅰ = ap (λ - → 𝒿 ∨[ 𝒪 Patch-𝕊 ] -) p
  Ⅱ = ap (λ - → 𝒿 ∨[ 𝒪 Patch-𝕊 ] -) closed-𝟏-is-top
  Ⅲ = 𝟏-right-annihilator-for-∨ (𝒪 Patch-𝕊) 𝒿
  Ⅳ = closed-𝟏-is-top ⁻¹

  † : 𝒿 ∨[ 𝒪 Patch-𝕊 ] 𝓀 ＝ closed-𝟏
  † = 𝒿 ∨[ 𝒪 Patch-𝕊 ] 𝓀               ＝⟨ Ⅰ ⟩
      𝒿 ∨[ 𝒪 Patch-𝕊 ] closed-𝟏        ＝⟨ Ⅱ ⟩
      𝒿 ∨[ 𝒪 Patch-𝕊 ] 𝟏[ 𝒪 Patch-𝕊 ]  ＝⟨ Ⅲ ⟩
      𝟏[ 𝒪 Patch-𝕊 ]                   ＝⟨ Ⅳ ⟩
      closed-𝟏                         ∎

case-lemma₂ : (i : index ℬ𝕊)
            → (is : index ℬ-patch-↑)
            → equal-to-one-of-the-four-compact-opensₚ (𝔬 i ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
case-lemma₂ i is = {!!}

basis-tetrachotomy-for-Patch-𝕊
 : (i : index ℬ-patch-↑)
 → equal-to-one-of-the-four-compact-opensₚ (ℬ-patch-↑ [ i ])
basis-tetrachotomy-for-Patch-𝕊 []       = inl †
 where
  † : 𝟎[ 𝒪 Patch-𝕊 ] ＝ closed-𝟎
  † = closed-𝟎-is-bottom ⁻¹
basis-tetrachotomy-for-Patch-𝕊 ((i , j) ∷ is) =
 cases₃ case₁ case₂ case₃ (basis-trichotomy i)
  where
   IH : equal-to-one-of-the-four-compact-opensₚ (ℬ-patch-↑ [ is ])
   IH = basis-tetrachotomy-for-Patch-𝕊 is

   case₁ : 𝜸 i ＝ 𝟏[ 𝒪 𝕊 ]
         → equal-to-one-of-the-four-compact-opensₚ (ℬ-patch-↑ [ (i , j) ∷ is ])
   case₁ p = transport equal-to-one-of-the-four-compact-opensₚ (q ⁻¹) γ
    where
     case₁a : 𝜸 j ＝ 𝟏[ 𝒪 𝕊 ]
            → equal-to-one-of-the-four-compact-opensₚ
               (𝔬 j ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
     case₁a q = transport equal-to-one-of-the-four-compact-opensₚ (r ⁻¹) IH
      where
       Ⅰ = ap (λ - → - ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]))
              (ap (λ - → ¬‘ - ’) (to-𝒦-＝ 𝕊 (𝜸-gives-compact-opens j) 𝕊-is-compact q))
       Ⅱ = ap (λ - → - ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ])) open-𝟏-is-bottom
       Ⅲ = 𝟎-right-unit-of-∨ (𝒪 Patch-𝕊) (ℬ-patch-↑ [ is ])

       r : 𝔬 j ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]) ＝ ℬ-patch-↑ [ is ]
       r = 𝔬 j ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ])             ＝⟨ Ⅰ ⟩
           open-𝟏 ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ])          ＝⟨ Ⅱ ⟩
           𝟎[ 𝒪 Patch-𝕊 ] ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ])  ＝⟨ Ⅲ ⟩
           ℬ-patch-↑ [ is ]                                  ∎

     case₁b : 𝜸 j ＝ truth
            → equal-to-one-of-the-four-compact-opensₚ
               (𝔬 j ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
     case₁b q = transport equal-to-one-of-the-four-compact-opensₚ (r ⁻¹) †
      where
       r : 𝔬 j ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]
           ＝ open-truth ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]
       r = ap
            (λ - → ¬‘ - ’ ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
            (to-𝒦-＝ 𝕊 (𝜸-gives-compact-opens j) truth-is-compact q)

       case₁b-α : ℬ-patch-↑ [ is ] ＝ closed-𝟎
                → equal-to-one-of-the-four-compact-opensₚ
                   (open-truth ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
       case₁b-α p = inr (inr (inl †))
        where
         Ⅰ = ap (λ - → open-truth ∨[ 𝒪 Patch-𝕊 ] -) p
         Ⅱ = ap (λ - → open-truth ∨[ 𝒪 Patch-𝕊 ] -) closed-𝟎-is-bottom
         Ⅲ = 𝟎-left-unit-of-∨ (𝒪 Patch-𝕊) open-truth

         † : open-truth ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ] ＝ open-truth
         † = open-truth ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ] ＝⟨ Ⅰ ⟩
             open-truth ∨[ 𝒪 Patch-𝕊 ] closed-𝟎         ＝⟨ Ⅱ ⟩
             open-truth ∨[ 𝒪 Patch-𝕊 ] 𝟎[ 𝒪 Patch-𝕊 ]   ＝⟨ Ⅲ ⟩
             open-truth                                 ∎

       case₁b-β : ℬ-patch-↑ [ is ] ＝ closed-truth
                → equal-to-one-of-the-four-compact-opensₚ
                   (open-truth ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]))
       case₁b-β p = inr (inr (inr †))
        where
         Ⅰ = ap (λ - → open-truth ∨[ 𝒪 Patch-𝕊 ] -) p
         Ⅱ = important-lemma
         Ⅲ = closed-𝟏-is-top ⁻¹

         † : open-truth ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]) ＝ closed-𝟏
         † = open-truth ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ])   ＝⟨ Ⅰ ⟩
             open-truth ∨[ 𝒪 Patch-𝕊 ] closed-truth         ＝⟨ Ⅱ ⟩
             𝟏[ 𝒪 Patch-𝕊 ]                                 ＝⟨ Ⅲ ⟩
             closed-𝟏                                       ∎

       case₁b-γ : ℬ-patch-↑ [ is ] ＝ open-truth
                → equal-to-one-of-the-four-compact-opensₚ
                   (open-truth ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]))
       case₁b-γ q = inr (inr (inl †))
        where
         Ⅰ = ap (λ - → open-truth ∨[ 𝒪 Patch-𝕊 ] -) q
         Ⅱ = ∨[ 𝒪 Patch-𝕊 ]-is-idempotent open-truth ⁻¹

         † : open-truth ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]) ＝ open-truth
         † = open-truth ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ])  ＝⟨ Ⅰ ⟩
             open-truth ∨[ 𝒪 Patch-𝕊 ] open-truth          ＝⟨ Ⅱ ⟩
             open-truth ∎

       case₁b-δ : ℬ-patch-↑ [ is ] ＝ closed-𝟏
                → equal-to-one-of-the-four-compact-opensₚ
                   (open-truth ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]))
       case₁b-δ = case-lemma₁ open-truth (ℬ-patch-↑ [ is ])

       † : equal-to-one-of-the-four-compact-opensₚ (open-truth ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]))
       † = cases₄ case₁b-α case₁b-β case₁b-γ case₁b-δ IH

     case₁c : 𝜸 j ＝ 𝟎[ 𝒪 𝕊 ]
            → equal-to-one-of-the-four-compact-opensₚ
               (𝔬 j ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
     case₁c q = transport equal-to-one-of-the-four-compact-opensₚ (r ⁻¹) †
      where
       Ⅰ = ap
            (λ - → ¬‘ - ’ ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
            (to-𝒦-＝ 𝕊 (𝜸-gives-compact-opens j) (𝟎-is-compact 𝕊) q)
       Ⅱ = ap (λ - → - ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]) open-𝟎-is-top
       Ⅲ = 𝟏-left-annihilator-for-∨ (𝒪 Patch-𝕊) (ℬ-patch-↑ [ is ])

       r : (𝔬 j ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]) ＝ 𝟏[ 𝒪 Patch-𝕊 ]
       r = 𝔬 j ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]                                 ＝⟨ refl ⟩
           ¬‘ 𝜸 j , 𝜸-gives-compact-opens j ’ ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]  ＝⟨ Ⅰ ⟩
           ¬‘ 𝟎[ 𝒪 𝕊 ] , 𝟎-is-compact 𝕊 ’ ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]      ＝⟨ Ⅱ ⟩
           𝟏[ 𝒪 Patch-𝕊 ] ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]                      ＝⟨ Ⅲ ⟩
           𝟏[ 𝒪 Patch-𝕊 ]                                                      ∎

       † : equal-to-one-of-the-four-compact-opensₚ 𝟏[ 𝒪 Patch-𝕊 ]
       † = inr (inr (inr (closed-𝟏-is-top ⁻¹)))

     γ : equal-to-one-of-the-four-compact-opensₚ
          (𝔬 j ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]))
     γ = cases₃ case₁a case₁b case₁c (basis-trichotomy j)

     q : ℬ-patch-↑ [ (i , j) ∷ is ] ＝ 𝔬 j ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]
     q =
      ℬ-patch-↑ [ (i , j) ∷ is ]                                           ＝⟨ Ⅰ ⟩
      (𝔠 i ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]             ＝⟨ Ⅱ ⟩
      (𝟏[ 𝒪 Patch-𝕊 ] ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]  ＝⟨ Ⅲ ⟩
      𝔬 j ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]                                  ∎
       where
        Ⅰ = refl
        Ⅱ = ap
             (λ - → (- ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
             (𝔠 i ＝⟨ ap (λ - → ‘ - ’) p ⟩ closed-𝟏 ＝⟨ closed-𝟏-is-top ⟩ 𝟏[ 𝒪 Patch-𝕊 ] ∎)
        Ⅲ = ap
             (λ - → - ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
             (𝟏-left-unit-of-∧ (𝒪 Patch-𝕊) (𝔬 j))

   case₂ : 𝜸 i ＝ truth
         → equal-to-one-of-the-four-compact-opensₚ (ℬ-patch-↑ [ i , j ∷ is ])
   case₂ p = transport equal-to-one-of-the-four-compact-opensₚ (q′ ⁻¹) †
    where
     q : (ℬ-patch-↑ [ (i , j) ∷ is ]) ＝ (𝔠 i ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]
     q = refl

     q′ : (ℬ-patch-↑ [ (i , j) ∷ is ]) ＝ (closed-truth ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]
     q′ = ap
           (λ - →
              binary-join (𝒪 Patch-𝕊) (meet-of (𝒪 Patch-𝕊) - (𝔬 j))
              (ℬ-patch-↑ [ is ]))
           (ap (λ - → ‘ - ’) p)

     case₂-a : 𝜸 j ＝ 𝟏[ 𝒪 𝕊 ]
             → equal-to-one-of-the-four-compact-opensₚ
                (closed-truth ∧[ 𝒪 Patch-𝕊 ] (𝔬 j) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
     case₂-a p = transport equal-to-one-of-the-four-compact-opensₚ (r ⁻¹) IH
      where
       Ⅰ = ap
            (λ - → (closed-truth ∧[ 𝒪 Patch-𝕊 ] ¬‘ - ’) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
            (to-𝒦-＝ 𝕊 (𝜸-gives-compact-opens j) 𝕊-is-compact p)
       Ⅱ = ap
            (λ - → ((closed-truth ∧[ 𝒪 Patch-𝕊 ] -) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]))
            open-𝟏-is-bottom
       Ⅲ = ap
            (λ - → - ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
            (𝟎-right-annihilator-for-∧ (𝒪 Patch-𝕊) closed-truth)
       Ⅳ = 𝟎-right-unit-of-∨ (𝒪 Patch-𝕊) (ℬ-patch-↑ [ is ])

       r : ((closed-truth ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
           ＝ (ℬ-patch-↑ [ is ])
       r = (closed-truth ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]
             ＝⟨ Ⅰ ⟩
          (closed-truth ∧[ 𝒪 Patch-𝕊 ] open-𝟏) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]
             ＝⟨ Ⅱ ⟩
          (closed-truth ∧[ 𝒪 Patch-𝕊 ] 𝟎[ 𝒪 Patch-𝕊 ]) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]
             ＝⟨ Ⅲ ⟩
          𝟎[ 𝒪 Patch-𝕊 ] ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ])
             ＝⟨ Ⅳ ⟩
          (ℬ-patch-↑ [ is ]) ∎

     case₂-b : 𝜸 j ＝ truth
             → equal-to-one-of-the-four-compact-opensₚ
                (closed-truth ∧[ 𝒪 Patch-𝕊 ] (𝔬 j) ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]))
     case₂-b = {!!}

     case₂-c : 𝜸 j ＝ 𝟎[ 𝒪 𝕊 ]
             → equal-to-one-of-the-four-compact-opensₚ
                (binary-join (𝒪 Patch-𝕊) (meet-of (𝒪 Patch-𝕊) closed-truth (𝔬 j)) (ℬ-patch-↑ [ is ]))
     case₂-c p = {!!}
      where
       r : ((closed-truth ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
           ＝ ((closed-truth ∧[ 𝒪 Patch-𝕊 ] 𝟏[ 𝒪 Patch-𝕊 ]) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
       r = (closed-truth ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ])
            ＝⟨ {!!} ⟩
           {!!} ∎

     † : equal-to-one-of-the-four-compact-opensₚ
          ((closed-truth ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]))
     † = cases₃ case₂-a case₂-b case₂-c (basis-trichotomy j)

   case₃ : 𝜸 i ＝ 𝟎[ 𝒪 𝕊 ]
         → equal-to-one-of-the-four-compact-opensₚ (ℬ-patch-↑ [ i , j ∷ is ])
   case₃ p = transport equal-to-one-of-the-four-compact-opensₚ († ⁻¹) IH
    where
     q : 𝔠 i ＝ closed-𝟎
     q = 𝔠 i ＝⟨ ap (λ - → ‘ - ’) p ⟩ closed-𝟎 ∎

     foo : 𝔠 i ∧[ 𝒪 Patch-𝕊 ] 𝔬 j ＝ closed-𝟎 ∧[ 𝒪 Patch-𝕊 ] 𝔬 j
     foo = ap (λ - → - ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) q

     † : ℬ-patch-↑ [ i , j ∷ is ] ＝ ℬ-patch-↑ [ is ]
     † = (𝔠 i ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]             ＝⟨ Ⅰ ⟩
         (‘ 𝟎[ 𝒪 𝕊 ] ’ ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]    ＝⟨ Ⅱ ⟩
         (𝟎[ 𝒪 Patch-𝕊 ] ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]  ＝⟨ Ⅲ ⟩
         𝟎[ 𝒪 Patch-𝕊 ] ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]                       ＝⟨ Ⅳ ⟩
         ℬ-patch-↑ [ is ]                                                     ∎
          where
           Ⅰ = ap
                (λ - → (- ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
                q
           Ⅱ = ap
                (λ - → (- ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
                closed-𝟎-is-bottom
           Ⅲ = ap
                (λ - → - ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
                (𝟎-left-annihilator-for-∧ (𝒪 Patch-𝕊) (𝔬 j))
           Ⅳ = 𝟎-right-unit-of-∨ (𝒪 Patch-𝕊) (ℬ-patch-↑ [ is ])

\end{code}
