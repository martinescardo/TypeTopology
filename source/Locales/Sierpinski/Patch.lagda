---
title:          The patch locale of the Sierpiński locale
author:         Ayberk Tosun
date-completed: 2024-02-12
---

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚; ₁)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

module Locales.Sierpinski.Patch
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
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤
open import DomainTheory.Basics.Dcpo    pt fe 𝓤 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Basics.Miscelanea pt fe 𝓤
open import DomainTheory.Basics.Pointed pt fe 𝓤 renaming (⊥ to ⊥∙)
open import DomainTheory.Basics.WayBelow pt fe 𝓤
open import DomainTheory.Lifting.LiftingSet pt fe 𝓤 pe
open import DomainTheory.Lifting.LiftingSetAlgebraic pt pe fe 𝓤
open import DomainTheory.Topology.ScottTopology pt fe 𝓤
open import Lifting.Miscelanea-PropExt-FunExt 𝓤 pe fe
open import Lifting.UnivalentPrecategory 𝓤 (𝟙 {𝓤})
open import Locales.Compactness pt fe
open import Locales.Complements pt fe
open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.DiscreteLocale.Definition fe pe pt
open import Locales.DiscreteLocale.Two fe pe pt
open import Locales.DiscreteLocale.Two-Properties fe pe pt sr 𝓤
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.Frame pt fe hiding (𝟚; is-directed)
open import Locales.HeytingImplication pt fe
open import Locales.InitialFrame pt fe
open import Locales.Sierpinski.Definition 𝓤 pe pt fe sr
open import Locales.Sierpinski.Properties 𝓤 pe pt fe sr
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.LatticeOfCompactOpens ua pt sr
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import Locales.Stone pt fe sr
open import MLTT.List hiding ([_])
open import MLTT.Sigma
open import Slice.Family
open import UF.Base
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

open AllCombinators pt fe

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

important-lemma′ : closed-truth ∨[ 𝒪 Patch-𝕊 ] open-truth ＝ 𝟏[ 𝒪 Patch-𝕊 ]
important-lemma′ = closed-truth ∨[ 𝒪 Patch-𝕊 ] open-truth   ＝⟨ Ⅰ ⟩
                   open-truth ∨[ 𝒪 Patch-𝕊 ] closed-truth   ＝⟨ Ⅱ ⟩
                   𝟏[ 𝒪 Patch-𝕊 ]                           ∎
                    where
                     Ⅰ = ∨[ 𝒪 Patch-𝕊 ]-is-commutative closed-truth open-truth
                     Ⅱ = important-lemma

important-lemma₂ : open-truth ∧[ 𝒪 Patch-𝕊 ] closed-truth ＝ 𝟎[ 𝒪 Patch-𝕊 ]
important-lemma₂ = pr₁ (closed-complements-open truth truth-is-compact)

important-lemma₂′ : closed-truth ∧[ 𝒪 Patch-𝕊 ] open-truth ＝ 𝟎[ 𝒪 Patch-𝕊 ]
important-lemma₂′ =
 closed-truth ∧[ 𝒪 Patch-𝕊 ] open-truth   ＝⟨ Ⅰ ⟩
 open-truth ∧[ 𝒪 Patch-𝕊 ] closed-truth   ＝⟨ Ⅱ ⟩
 𝟎[ 𝒪 Patch-𝕊 ]                           ∎
  where
   Ⅰ = ∧[ 𝒪 Patch-𝕊 ]-is-commutative closed-truth open-truth
   Ⅱ = important-lemma₂

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
     case₂-b p = transport equal-to-one-of-the-four-compact-opensₚ (r ⁻¹) IH
      where
       Ⅰ = ap
            (λ - →
               binary-join (𝒪 Patch-𝕊) (meet-of (𝒪 Patch-𝕊) closed-truth -)
               (ℬ-patch-↑ [ is ]))
            (ap (λ - → ¬‘ - ’) (to-𝒦-＝ 𝕊 (𝜸-gives-compact-opens j) truth-is-compact p))
       Ⅱ = ap (λ - → (- ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])) important-lemma₂′
       Ⅲ = 𝟎-right-unit-of-∨ (𝒪 Patch-𝕊) (ℬ-patch-↑ [ is ])

       r : (closed-truth ∧[ 𝒪 Patch-𝕊 ] 𝔬 j ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
           ＝ ℬ-patch-↑ [ is ]
       r = ((closed-truth ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
             ＝⟨ Ⅰ ⟩
           ((closed-truth ∧[ 𝒪 Patch-𝕊 ] open-truth) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
             ＝⟨ Ⅱ ⟩
           (𝟎[ 𝒪 Patch-𝕊 ] ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
             ＝⟨ Ⅲ ⟩
           ℬ-patch-↑ [ is ]
             ∎

     case₂-c : 𝜸 j ＝ 𝟎[ 𝒪 𝕊 ]
             → equal-to-one-of-the-four-compact-opensₚ
                ((closed-truth ∧[ 𝒪 Patch-𝕊 ] (𝔬 j)) ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]))
     case₂-c p = transport equal-to-one-of-the-four-compact-opensₚ (r ⁻¹) ‡
      where
       case₂-c-α : ℬ-patch-↑ [ is ] ＝ closed-𝟎 →
                    equal-to-one-of-the-four-compact-opensₚ
                    (binary-join (𝒪 Patch-𝕊) closed-truth (ℬ-patch-↑ [ is ]))
       case₂-c-α q = inr (inl †)
        where
         Ⅰ = ap (λ - → closed-truth ∨[ 𝒪 Patch-𝕊 ] -) q
         Ⅱ = ap (λ - → closed-truth ∨[ 𝒪 Patch-𝕊 ] -) closed-𝟎-is-bottom
         Ⅲ = 𝟎-left-unit-of-∨ (𝒪 Patch-𝕊) closed-truth

         † : closed-truth ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ] ＝ closed-truth
         † = closed-truth ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]   ＝⟨ Ⅰ ⟩
             closed-truth ∨[ 𝒪 Patch-𝕊 ] closed-𝟎           ＝⟨ Ⅱ ⟩
             closed-truth ∨[ 𝒪 Patch-𝕊 ] 𝟎[ 𝒪 Patch-𝕊 ]     ＝⟨ Ⅲ ⟩
             closed-truth                                   ∎

       case₂-c-β : ℬ-patch-↑ [ is ] ＝ closed-truth →
                    equal-to-one-of-the-four-compact-opensₚ
                    (binary-join (𝒪 Patch-𝕊) closed-truth (ℬ-patch-↑ [ is ]))
       case₂-c-β q = inr (inl †)
        where
         Ⅰ = ap (λ - → closed-truth ∨[ 𝒪 Patch-𝕊 ] -) q
         Ⅱ = ∨[ 𝒪 Patch-𝕊 ]-is-idempotent closed-truth ⁻¹

         † : closed-truth ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]) ＝ closed-truth
         † = closed-truth ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ])  ＝⟨ Ⅰ ⟩
             closed-truth ∨[ 𝒪 Patch-𝕊 ] closed-truth        ＝⟨ Ⅱ ⟩
             closed-truth                                    ∎

       case₂-c-γ : ℬ-patch-↑ [ is ] ＝ open-truth
                 → equal-to-one-of-the-four-compact-opensₚ
                    (closed-truth ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]))
       case₂-c-γ p = inr (inr (inr †))
        where
         Ⅰ = ap (λ - → closed-truth ∨[ 𝒪 Patch-𝕊 ] -) p
         Ⅱ = important-lemma′

         r : closed-truth ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]) ＝ 𝟏[ 𝒪 Patch-𝕊 ]
         r = closed-truth ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]) ＝⟨ Ⅰ ⟩
             closed-truth ∨[ 𝒪 Patch-𝕊 ] open-truth         ＝⟨ Ⅱ ⟩
             𝟏[ 𝒪 Patch-𝕊 ]                                 ∎

         † : closed-truth ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]) ＝ closed-𝟏
         † = closed-truth ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]) ＝⟨ r ⟩
             𝟏[ 𝒪 Patch-𝕊 ]                                 ＝⟨ closed-𝟏-is-top ⁻¹ ⟩
             closed-𝟏                                        ∎

       case₂-c-δ : ℬ-patch-↑ [ is ] ＝ closed-𝟏 →
                    equal-to-one-of-the-four-compact-opensₚ
                    (binary-join (𝒪 Patch-𝕊) closed-truth (ℬ-patch-↑ [ is ]))
       case₂-c-δ = case-lemma₁ closed-truth (ℬ-patch-↑ [ is ])

       Ⅰ = ap
            (λ - → closed-truth ∧[ 𝒪 Patch-𝕊 ] ¬‘ - ’ ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]))
            (to-𝒦-＝ 𝕊 (𝜸-gives-compact-opens j) (𝟎-is-compact 𝕊) p)
       Ⅱ = ap
            (λ - → (closed-truth ∧[ 𝒪 Patch-𝕊 ] -) ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ]))
            open-𝟎-is-top
       Ⅲ = ap (λ - → - ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ])) (𝟏-right-unit-of-∧ (𝒪 Patch-𝕊) closed-truth)

       r : ((closed-truth ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
           ＝ (closed-truth ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
       r = (closed-truth ∧[ 𝒪 Patch-𝕊 ] 𝔬 j) ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ])
            ＝⟨ Ⅰ ⟩
           (closed-truth ∧[ 𝒪 Patch-𝕊 ] open-𝟎) ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ])
            ＝⟨ Ⅱ ⟩
           (closed-truth ∧[ 𝒪 Patch-𝕊 ] 𝟏[ 𝒪 Patch-𝕊 ]) ∨[ 𝒪 Patch-𝕊 ] (ℬ-patch-↑ [ is ])
            ＝⟨ Ⅲ ⟩
           closed-truth ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ]
            ∎

       ‡ : equal-to-one-of-the-four-compact-opensₚ
            (closed-truth ∨[ 𝒪 Patch-𝕊 ] ℬ-patch-↑ [ is ])
       ‡ = cases₄ case₂-c-α case₂-c-β case₂-c-γ case₂-c-δ IH

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

\begin{code}

𝟚-is-spectral-with-ssb : is-spectral-with-small-basis ua (𝟚-loc 𝓤) holds
𝟚-is-spectral-with-ssb = spectralᴰ-implies-ssb ua (𝟚-loc 𝓤) †
 where
  p : 𝟏[ 𝒪 𝟚ₗ ] ＝ 𝟏[ 𝒪 𝟚ₗ ] ∨[ 𝒪 𝟚ₗ ] 𝟎[ 𝒪 𝟚ₗ ]
  p = 𝟏-left-annihilator-for-∨ (𝒪 𝟚ₗ) 𝟎[ 𝒪 𝟚ₗ ] ⁻¹

  ζ : is-top (𝒪 (𝟚-loc 𝓤)) (𝟏[ 𝒪 𝟚ₗ ] ∨[ 𝒪 𝟚ₗ ] 𝟎[ 𝒪 𝟚ₗ ]) holds
  ζ = transport (λ - → is-top (𝒪 (𝟚-loc 𝓤)) - holds) p (𝟏-is-top (𝒪 𝟚ₗ))

  γ : contains-top (𝒪 (𝟚-loc 𝓤)) ℬ-𝟚↑ holds
  γ = ∣ ((₁ , ₁) ∷ []) , ζ ∣

  δ : closed-under-binary-meets (𝒪 (𝟚-loc 𝓤)) ℬ-𝟚↑ holds
  δ = {!!}

  † : spectralᴰ (𝟚-loc 𝓤)
  † = ℬ-𝟚↑ , ℬ-𝟚↑-is-directed-basis , ℬ-𝟚↑-is-spectral , (γ , δ)

\end{code}

\begin{code}

open 𝒦-Lattice (𝟚-loc 𝓤) 𝟚-is-spectral-with-ssb using () renaming (𝒦⦅X⦆ to 𝒦𝟚)

patch-𝕊-is-ssb : is-spectral-with-small-basis ua Patch-𝕊 holds
patch-𝕊-is-ssb = spectralᴰ-implies-ssb ua Patch-𝕊 patchₛ-spectralᴰ

open 𝒦-Lattice Patch-𝕊 patch-𝕊-is-ssb using () renaming (𝒦⦅X⦆ to 𝒦-Patch-𝕊)

\end{code}

\begin{code}

open DefnOfScottTopology 𝕊𝓓 𝓤

truth-is-not-zero : ¬ (truth ＝ 𝟎[ 𝒪 𝕊 ])
truth-is-not-zero p = 𝟘-is-not-𝟙 ( pr₁ (from-Σ-＝ q′) ⁻¹)
 where
  bar : Ω 𝓤
  bar = 𝟎[ 𝒪 𝕊 ] .pr₁ (to-𝕊𝓓 (𝟙 , 𝟙-is-prop))

  r : pr₁ truth ＝ pr₁ 𝟎[ 𝒪 𝕊 ]
  r = pr₁ (from-Σ-＝ p)

  † : (x : ⟨ 𝕊𝓓 ⟩∙) → 𝟎[ 𝒪 𝕊 ] .pr₁ x ＝ 𝟘 , 𝟘-is-prop
  † x = to-subtype-＝ (λ _ → being-prop-is-prop fe) ‡
   where
    h : ∥ Σ i ꞉ index (∅ 𝓤) , pr₁ (∅ {A = ⟨ 𝒪 𝕊 ⟩} 𝓤 [ i ]) x holds ∥ → 𝟘
    h = ∥∥-rec 𝟘-is-prop λ p → 𝟘-elim (pr₁ p)

    ‡ : ∥ Sigma (index (∅ 𝓤)) (λ i → pr₁ (∅ {A = ⟨ 𝒪 𝕊 ⟩} 𝓤 [ i ]) x holds) ∥ ＝ 𝟘
    ‡ = pe ∥∥-is-prop 𝟘-is-prop h (λ ())

  q : (x : ⟨ 𝕊𝓓 ⟩∙) → truth₀ x ＝ to-Ω x
  q x@(a , pr₃ , pr₄) = to-subtype-＝ (λ _ → being-prop-is-prop fe) refl

  r′ : (x : ⟨ 𝕊𝓓 ⟩∙) → truth₀ x ＝ 𝟘 , 𝟘-is-prop
  r′ x = transport (λ - → - x ＝ 𝟘 , 𝟘-is-prop) (r ⁻¹) († x)

  q′ : truth₀ (to-𝕊𝓓 ⊤) ＝ ⊥
  q′ = r′ (to-𝕊𝓓 (𝟙 , 𝟙-is-prop))

ext-eq : (𝒿 𝓀 : ⟨ 𝒪 Patch-𝕊 ⟩) → 𝒿 ＝ 𝓀 → (U : ⟨ 𝒪 𝕊 ⟩) → 𝒿 .pr₁ U ＝ 𝓀 .pr₁ U
ext-eq 𝒿 𝓀 p U = ap (λ - → - U) q
 where
  q : 𝒿 .pr₁ ＝ 𝓀 .pr₁
  q = pr₁ (from-Σ-＝ p)

truth-is-not-𝟏 : ¬ (truth ＝ 𝟏[ 𝒪 𝕊 ])
truth-is-not-𝟏 p = 𝟘-elim (equal-⊤-gives-holds ⊥ bar)
 where
  foo : truth .pr₁ ＝ 𝟏[ 𝒪 𝕊 ] .pr₁
  foo = pr₁ (from-Σ-＝ p)

  † : (x : ⟨ 𝕊𝓓 ⟩∙) → truth₀ x ＝ ⊤
  † x = ap (λ - → - x) foo

  bar : truth₀ (to-𝕊𝓓 ⊥) ＝ ⊤
  bar = † (to-𝕊𝓓 ⊥)

closed-truth-is-not-closed-𝟎 : ¬ (closed-truth ＝ closed-𝟎)
closed-truth-is-not-closed-𝟎 p = truth-is-not-zero †
 where
  Ⅰ = 𝟎-left-unit-of-∨ (𝒪 𝕊) truth ⁻¹
  Ⅱ = ext-eq closed-truth closed-𝟎 p 𝟎[ 𝒪 𝕊 ]
  Ⅲ = ∨[ 𝒪 𝕊 ]-is-idempotent 𝟎[ 𝒪 𝕊 ] ⁻¹

  † : truth ＝ 𝟎[ 𝒪 𝕊 ]
  † = truth                        ＝⟨ Ⅰ ⟩
      truth ∨[ 𝒪 𝕊 ] 𝟎[ 𝒪 𝕊 ]      ＝⟨ Ⅱ ⟩
      𝟎[ 𝒪 𝕊 ] ∨[ 𝒪 𝕊 ] 𝟎[ 𝒪 𝕊 ]   ＝⟨ Ⅲ ⟩
      𝟎[ 𝒪 𝕊 ]                     ∎

closed-truth-is-not-closed-𝟏 : ¬ (closed-truth ＝ closed-𝟏)
closed-truth-is-not-closed-𝟏 p = truth-is-not-𝟏 †
 where
  Ⅰ = ∨[ 𝒪 𝕊 ]-is-idempotent truth
  Ⅱ = ext-eq closed-truth closed-𝟏 p truth
  Ⅲ = 𝟏-left-annihilator-for-∨ (𝒪 𝕊) truth

  † : truth ＝ 𝟏[ 𝒪 𝕊 ]
  † = truth                     ＝⟨ Ⅰ ⟩
      truth ∨[ 𝒪 𝕊 ] truth      ＝⟨ Ⅱ ⟩
      𝟏[ 𝒪 𝕊 ] ∨[ 𝒪 𝕊 ] truth   ＝⟨ Ⅲ ⟩
      𝟏[ 𝒪 𝕊 ]                  ∎

open-truth-is-not-closed-𝟎 : ¬ (open-truth ＝ closed-𝟎)
open-truth-is-not-closed-𝟎 p = truth-is-not-𝟏 s
 where
  r : (truth ==> truth) ＝ 𝟏[ 𝒪 𝕊 ]
  r = heyting-implication-identity truth

  q : (truth ==> truth) ＝ 𝟎[ 𝒪 𝕊 ] ∨[ 𝒪 𝕊 ] truth
  q = ext-eq open-truth closed-𝟎 p truth

  Ⅰ = 𝟎-right-unit-of-∨ (𝒪 𝕊) truth ⁻¹
  Ⅱ = q ⁻¹
  Ⅲ = r

  s : truth ＝ 𝟏[ 𝒪 𝕊 ]
  s = truth                     ＝⟨ Ⅰ ⟩
      𝟎[ 𝒪 𝕊 ] ∨[ 𝒪 𝕊 ] truth   ＝⟨ Ⅱ ⟩
      (truth ==> truth)         ＝⟨ Ⅲ ⟩
      𝟏[ 𝒪 𝕊 ]                  ∎
-- TODO: Use the fact that `truth ==> truth` is 1 which is not 0.

open-truth-is-not-bottom : ¬ (open-truth ＝ 𝟎[ 𝒪 Patch-𝕊 ])
open-truth-is-not-bottom p = open-truth-is-not-closed-𝟎 †
 where
  † : open-truth ＝ closed-𝟎
  † = open-truth ＝⟨ p ⟩ 𝟎[ 𝒪 Patch-𝕊 ] ＝⟨ closed-𝟎-is-bottom ⁻¹ ⟩ closed-𝟎 ∎

closed-truth-is-not-bottom : ¬ (closed-truth ＝ 𝟎[ 𝒪 Patch-𝕊 ])
closed-truth-is-not-bottom p = closed-truth-is-not-closed-𝟎 †
 where
  † : closed-truth ＝ closed-𝟎
  † = closed-truth    ＝⟨ p ⟩
      𝟎[ 𝒪 Patch-𝕊 ]  ＝⟨ closed-𝟎-is-bottom ⁻¹ ⟩
      closed-𝟎        ∎

open-truth-is-not-closed-𝟏 : ¬ (open-truth ＝ closed-𝟏)
open-truth-is-not-closed-𝟏 p = closed-truth-is-not-bottom bb
 where
  γ : truth ==> 𝟎[ 𝒪 𝕊 ] ＝ 𝟏[ 𝒪 𝕊 ] ∨[ 𝒪 𝕊 ] 𝟎[ 𝒪 𝕊 ]
  γ = ext-eq open-truth closed-𝟏 p 𝟎[ 𝒪 𝕊 ]

  Ⅰ = ap (λ - → closed-truth ∧[ 𝒪 Patch-𝕊 ] -) (p ⁻¹)

  aa : closed-truth ∧[ 𝒪 Patch-𝕊 ] closed-𝟏 ＝ 𝟎[ 𝒪 Patch-𝕊 ]
  aa = closed-truth ∧[ 𝒪 Patch-𝕊 ] closed-𝟏    ＝⟨ Ⅰ ⟩
       closed-truth ∧[ 𝒪 Patch-𝕊 ] open-truth  ＝⟨ important-lemma₂′ ⟩
       𝟎[ 𝒪 Patch-𝕊 ]                          ∎

  Ⅱ = 𝟏-right-unit-of-∧ (𝒪 Patch-𝕊) closed-truth ⁻¹
  Ⅲ = ap (λ - → closed-truth ∧[ 𝒪 Patch-𝕊 ] -) (closed-𝟏-is-top ⁻¹)

  bb : closed-truth ＝ 𝟎[ 𝒪 Patch-𝕊 ]
  bb = closed-truth                                 ＝⟨ Ⅱ ⟩
       closed-truth ∧[ 𝒪 Patch-𝕊 ] 𝟏[ 𝒪 Patch-𝕊 ]   ＝⟨ Ⅲ ⟩
       closed-truth ∧[ 𝒪 Patch-𝕊 ] closed-𝟏         ＝⟨ aa ⟩
       𝟎[ 𝒪 Patch-𝕊 ]                               ∎

-- TODO: Use the fact that `truth ==> 1` is 1 which is not 0.

𝟏𝕊-is-not-𝟎𝕊 : ¬ (𝟏[ 𝒪 𝕊 ] ＝ 𝟎[ 𝒪 𝕊 ])
𝟏𝕊-is-not-𝟎𝕊 r = χ μ
 where
  χ : ¬ ((to-𝕊𝓓 ⊤ ∈ₛ 𝟎[ 𝒪 𝕊 ]) holds)
  χ = ∥∥-rec 𝟘-is-prop (λ ())

  μ : (to-𝕊𝓓 ⊤ ∈ₛ 𝟎[ 𝒪 𝕊 ]) holds
  μ = transport (λ - → (to-𝕊𝓓 ⊤ ∈ₛ -) holds) r ⋆

𝟏-is-not-𝟎-in-Patch-𝕊 : ¬ (𝟏[ 𝒪 Patch-𝕊 ] ＝ 𝟎[ 𝒪 Patch-𝕊 ])
𝟏-is-not-𝟎-in-Patch-𝕊 p = 𝟏𝕊-is-not-𝟎𝕊 δ
 where
  γ : (U : ⟨ 𝒪 𝕊 ⟩) → 𝟏[ 𝒪 Patch-𝕊 ] .pr₁ U ＝ 𝟎[ 𝒪 Patch-𝕊 ] .pr₁ U
  γ U = transport (λ - → - .pr₁ U ＝ 𝟎[ 𝒪 Patch-𝕊 ] .pr₁ U) (p ⁻¹) refl

  foo : 𝟏[ 𝒪 Patch-𝕊 ] .pr₁ 𝟎[ 𝒪 𝕊 ] ＝ 𝟏[ 𝒪 𝕊 ]
  foo = refl

  Ⅱ : 𝟎[ 𝒪 Patch-𝕊 ] .pr₁ 𝟎[ 𝒪 𝕊 ] ＝ 𝟎[ 𝒪 𝕊 ]
  Ⅱ = 𝟎-is-id 𝟎[ 𝒪 𝕊 ]

  δ : 𝟏[ 𝒪 𝕊 ] ＝ 𝟎[ 𝒪 𝕊 ]
  δ = 𝟏[ 𝒪 𝕊 ] ＝⟨ γ 𝟎[ 𝒪 𝕊 ] ⟩ 𝟎[ 𝒪 Patch-𝕊 ] .pr₁ 𝟎[ 𝒪 𝕊 ] ＝⟨ Ⅱ ⟩ 𝟎[ 𝒪 𝕊 ] ∎

closed-𝟏-is-not-closed-𝟎 : ¬ (closed-𝟏 ＝ closed-𝟎)
closed-𝟏-is-not-closed-𝟎 p = 𝟏-is-not-𝟎-in-Patch-𝕊 †
 where
  Ⅰ = closed-𝟏-is-top ⁻¹
  Ⅱ = p
  Ⅲ = closed-𝟎-is-bottom

  † : 𝟏[ 𝒪 Patch-𝕊 ] ＝ 𝟎[ 𝒪 Patch-𝕊 ]
  † = 𝟏[ 𝒪 Patch-𝕊 ]   ＝⟨ Ⅰ ⟩
      closed-𝟏         ＝⟨ Ⅱ ⟩
      closed-𝟎         ＝⟨ Ⅲ ⟩
      𝟎[ 𝒪 Patch-𝕊 ]   ∎

open-truth-is-not-closed-truth : ¬ (open-truth ＝ closed-truth)
open-truth-is-not-closed-truth p = open-truth-is-not-bottom s
 where
  q : open-truth ∧[ 𝒪 Patch-𝕊 ] closed-truth ＝ 𝟎[ 𝒪 Patch-𝕊 ]
  q = important-lemma₂

  Ⅰ = ∧[ 𝒪 Patch-𝕊 ]-is-idempotent open-truth
  Ⅱ = ap (λ - → open-truth ∧[ 𝒪 Patch-𝕊 ] -) p

  s : open-truth ＝ 𝟎[ 𝒪 Patch-𝕊 ]
  s = open-truth                              ＝⟨ Ⅰ ⟩
      open-truth ∧[ 𝒪 Patch-𝕊 ] open-truth    ＝⟨ Ⅱ ⟩
      open-truth ∧[ 𝒪 Patch-𝕊 ] closed-truth  ＝⟨ q ⟩
      𝟎[ 𝒪 Patch-𝕊 ]                          ∎

being-equal-to-one-of-the-four-compact-opens-is-prop : (𝒿 : ⟨ 𝒪 Patch-𝕊 ⟩)
                     → is-prop (equal-to-one-of-the-four-compact-opensₚ 𝒿)
being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿 (inl p) (inl q)       = ap inl (carrier-of-[ poset-of (𝒪 Patch-𝕊) ]-is-set p q)
being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿 (inl p) (inr (inl q)) = 𝟘-elim (closed-truth-is-not-closed-𝟎 †)
 where
  † : closed-truth ＝ closed-𝟎
  † = closed-truth ＝⟨ q ⁻¹ ⟩ 𝒿 ＝⟨ p ⟩ closed-𝟎 ∎
being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿 (inl p) (inr (inr (inl q))) = 𝟘-elim (open-truth-is-not-closed-𝟎 †)
 where
  † : open-truth ＝ closed-𝟎
  † = open-truth ＝⟨ q ⁻¹ ⟩ 𝒿 ＝⟨ p ⟩ closed-𝟎 ∎
being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿 (inl p) (inr (inr (inr q))) = 𝟘-elim (closed-𝟏-is-not-closed-𝟎 †)
 where
  † : closed-𝟏 ＝ closed-𝟎
  † = closed-𝟏 ＝⟨ q ⁻¹ ⟩ 𝒿 ＝⟨ p ⟩ closed-𝟎 ∎
being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿 (inr (inl p)) (inl q) = 𝟘-elim (closed-truth-is-not-closed-𝟎 †)
 where
  † : closed-truth ＝ closed-𝟎
  † = closed-truth ＝⟨ p ⁻¹ ⟩ 𝒿 ＝⟨ q ⟩ closed-𝟎 ∎
being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿 (inr (inr (inl p))) (inl q) = 𝟘-elim (open-truth-is-not-closed-𝟎 †)
 where
  † : open-truth ＝ closed-𝟎
  † = open-truth ＝⟨ p ⁻¹ ⟩ 𝒿 ＝⟨ q ⟩ closed-𝟎 ∎
being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿 (inr (inr (inr p))) (inl q) = 𝟘-elim (closed-𝟏-is-not-closed-𝟎 †)
 where
  † : closed-𝟏 ＝ closed-𝟎
  † = closed-𝟏 ＝⟨ p ⁻¹ ⟩ 𝒿 ＝⟨ q ⟩ closed-𝟎 ∎
being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿 (inr (inl p)) (inr (inl q)) = ap (inr ∘ inl) (carrier-of-[ poset-of (𝒪 Patch-𝕊) ]-is-set p q)
being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿 (inr (inl p)) (inr (inr (inl q))) = 𝟘-elim (open-truth-is-not-closed-truth †)
 where
  † : open-truth ＝ closed-truth
  † = open-truth ＝⟨ q ⁻¹ ⟩ 𝒿 ＝⟨ p ⟩ closed-truth ∎
being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿 (inr (inl p)) (inr (inr (inr q))) = 𝟘-elim (closed-truth-is-not-closed-𝟏 †)
 where
  † : closed-truth ＝ closed-𝟏
  † = closed-truth ＝⟨ p ⁻¹ ⟩ 𝒿 ＝⟨ q ⟩ closed-𝟏 ∎
being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿 (inr (inr (inl p))) (inr (inl q)) = 𝟘-elim (open-truth-is-not-closed-truth †)
 where
  † : open-truth ＝ closed-truth
  † = open-truth ＝⟨ p ⁻¹ ⟩ 𝒿 ＝⟨ q ⟩ closed-truth ∎
being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿 (inr (inr (inr p))) (inr (inl q)) = 𝟘-elim (closed-truth-is-not-closed-𝟏 †)
 where
  † : closed-truth ＝ closed-𝟏
  † = closed-truth ＝⟨ q ⁻¹ ⟩ 𝒿 ＝⟨ p ⟩ closed-𝟏 ∎
being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿 (inr (inr (inl p))) (inr (inr (inl q))) = ap (inr ∘ inr ∘ inl) (carrier-of-[ poset-of (𝒪 Patch-𝕊) ]-is-set p q)
being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿 (inr (inr (inl p))) (inr (inr (inr q))) = 𝟘-elim (open-truth-is-not-closed-𝟏 †)
 where
  † : open-truth ＝ closed-𝟏
  † = open-truth ＝⟨ p ⁻¹ ⟩ 𝒿 ＝⟨ q ⟩ closed-𝟏 ∎
being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿 (inr (inr (inr p))) (inr (inr (inl q))) = 𝟘-elim (open-truth-is-not-closed-𝟏 †)
 where
  † : open-truth ＝ closed-𝟏
  † = open-truth ＝⟨ q ⁻¹ ⟩ 𝒿 ＝⟨ p ⟩ closed-𝟏 ∎
being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿 (inr (inr (inr p))) (inr (inr (inr q))) = ap (inr ∘ inr ∘ inr) (carrier-of-[ poset-of (𝒪 Patch-𝕊) ]-is-set p q)

is-equal-to-one-of-the-four-compact-opens : ⟨ 𝒪 Patch-𝕊 ⟩ → Ω (𝓤 ⁺)
is-equal-to-one-of-the-four-compact-opens 𝒿 =
 equal-to-one-of-the-four-compact-opensₚ 𝒿 , being-equal-to-one-of-the-four-compact-opens-is-prop 𝒿

\end{code}

Added on 2024-07-13.

\begin{code}

compact-tetrachotomy-for-Patch-𝕊
 : (𝒿 : ⟨ 𝒪 Patch-𝕊 ⟩)
 → is-compact-open Patch-𝕊 𝒿 holds
 → equal-to-one-of-the-four-compact-opensₚ 𝒿
compact-tetrachotomy-for-Patch-𝕊 𝒿 κ =
 ∥∥-rec (holds-is-prop (is-equal-to-one-of-the-four-compact-opens 𝒿)) † γ
  where
   † : (Σ is ꞉ (index ℬ-patch-↑) , (ℬ-patch-↑ [ is ]) ＝ 𝒿)
     → is-equal-to-one-of-the-four-compact-opens 𝒿 holds
   † (is , p) = transport equal-to-one-of-the-four-compact-opensₚ p δ
    where
     δ : equal-to-one-of-the-four-compact-opensₚ (ℬ-patch-↑ [ is ])
     δ = basis-tetrachotomy-for-Patch-𝕊 is

   γ : is-basic Patch-𝕊 𝒿 (ℬ-patch-↑ , ℬ-patchₛ-β↑) holds
   γ = compact-opens-are-basic Patch-𝕊 (ℬ-patch-↑ , ℬ-patchₛ-β↑) 𝒿 κ

\end{code}

\begin{code}

to-𝒦𝟚 : ∣ 𝒦-Patch-𝕊 ∣ᵈ → ∣ 𝒦𝟚 ∣ᵈ
to-𝒦𝟚 (𝒿 , κ) = cases₄ case₁ case₂ case₃ case₄ γ
 where
  γ : equal-to-one-of-the-four-compact-opensₚ 𝒿
  γ = compact-tetrachotomy-for-Patch-𝕊 𝒿 κ

  case₁ : 𝒿 ＝ closed-𝟎 → ∣ 𝒦𝟚 ∣ᵈ
  case₁ _ = 𝟎[ 𝒪 𝟚ₗ ] , 𝟎-is-compact 𝟚ₗ

  case₂ : 𝒿 ＝ closed-truth → ∣ 𝒦𝟚 ∣ᵈ
  case₂ _ = trueₖ , trueₖ-is-compact

  case₃ : 𝒿 ＝ open-truth → ∣ 𝒦𝟚 ∣ᵈ
  case₃ _ = falseₖ , falseₖ-is-compact

  case₄ : 𝒿 ＝ closed-𝟏 → ∣ 𝒦𝟚 ∣ᵈ
  case₄ _ = 𝟏[ 𝒪 𝟚ₗ ] , 𝟚ₗ-is-compact

to-patch-𝕊 : ∣ 𝒦𝟚 ∣ᵈ → ∣ 𝒦-Patch-𝕊 ∣ᵈ
to-patch-𝕊 (U , κ) = {!!}
 where
  γ : ∥ equal-to-one-of-the-four-compact-opens U ∥
  γ = compact-tetrachotomy U κ

  † : equal-to-one-of-the-four-compact-opens U
  † = {!exit-∥∥ !}

\end{code}
