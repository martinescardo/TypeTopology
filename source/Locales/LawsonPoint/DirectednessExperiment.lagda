--------------------------------------------------------------------------------
author:       Ayberk Tosun
date-started: 2024-03-15
--------------------------------------------------------------------------------

Let `D` be a Scott domain satisfying the condition that upper boundedness of
compact opens is decidable, and denote by `σ(D)` the Scott locale of `D`.

By a “point” of `D`, we mean a frame homomorphism `F : 𝒪(σ(D)) → Ω`.

In this module, we define the family

  { c : 𝒦(D) ∣ ↑(c) ∈ F }

and prove that it is directed.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons

module Locales.LawsonPoint.DirectednessExperiment
        (𝓤  : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓤
open import DomainTheory.BasesAndContinuity.ScottDomain      pt fe 𝓤
open import DomainTheory.Basics.Dcpo pt fe 𝓤 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Basics.Pointed pt fe 𝓤
open import DomainTheory.Basics.WayBelow pt fe 𝓤
open import DomainTheory.Topology.ScottTopology pt fe 𝓤
open import DomainTheory.Topology.ScottTopologyProperties pt fe 𝓤
open import Locales.Compactness pt fe hiding (is-compact)
open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Ideal pt fe pe hiding (is-inhabited)
open import Locales.DistributiveLattice.Properties fe pt
open import Locales.Frame pt fe hiding (is-directed)
open import Locales.InitialFrame pt fe
open import Locales.ScottLocale.Definition pt fe 𝓤
open import Locales.ScottLocale.Properties pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfScottDomains pt fe sr 𝓤
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralMap pt fe
open import Locales.TerminalLocale.Properties pt fe sr
open import MLTT.Fin hiding (𝟎; 𝟏)
open import MLTT.List hiding ([_])
open import Slice.Family
open import UF.Logic
open import UF.Powerset
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier renaming (⊥ to ⊥ₚ)
open import UF.Univalence

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)
open Locale
open PropositionalTruncation pt hiding (_∨_)
open FrameHomomorphisms

\end{code}

\begin{code}

module Preliminaries (X : Locale (𝓤 ⁺) 𝓤 𝓤) where

 open ContinuousMaps

 𝟏L : Locale (𝓤 ⁺) 𝓤 𝓤
 𝟏L = 𝟏Loc pe

 Point : 𝓤 ⁺  ̇
 Point = 𝟏L ─c→  X

 SpecPoint : 𝓤 ⁺  ̇
 SpecPoint = Σ F ꞉ 𝟏L ─c→ X , is-spectral-map X 𝟏L F holds

\end{code}

\begin{code}

open DefinitionOfScottDomain

module Experiment
        (𝓓    : DCPO {𝓤 ⁺} {𝓤})
        (ua   : Univalence)
        (hl   : has-least (underlying-order 𝓓))
        (sd   : is-scott-domain 𝓓 holds)
        (dc   : decidability-condition 𝓓) where

 open SpectralScottLocaleConstruction₂ 𝓓 ua hl sd dc pe
 open SpectralScottLocaleConstruction 𝓓 hl hscb dc bc pe hiding (scb; β; ϟ)
 open DefnOfScottTopology 𝓓 𝓤
 open Properties 𝓓

 open Preliminaries σ⦅𝓓⦆

 B𝓓 : Fam 𝓤 ⟨ 𝓓 ⟩∙
 B𝓓 = index-of-compact-basis 𝓓 hscb , family-of-compact-elements 𝓓 hscb

 scb : is-small-compact-basis 𝓓 (family-of-compact-elements 𝓓 hscb)
 scb = small-compact-basis 𝓓 hscb

 open is-small-compact-basis scb

 open BottomLemma 𝓓 𝕒 hl

 βₖ : (i : index B𝓓) → Σ c ꞉ ⟨ 𝓓 ⟩∙ , is-compact 𝓓 c
 βₖ i = B𝓓 [ i ] , basis-is-compact i

 compact-opens-of : Point → Fam 𝓤 ⟨ 𝓓 ⟩∙
 compact-opens-of ℱ =
  ⁅ B𝓓 [ c ] ∣ (c , _) ∶ Σ i ꞉ index B𝓓 , ↑ˢ[ βₖ i ] ∈ₚ F holds ⁆
   where
    F : ⟨ 𝒪 σ⦅𝓓⦆ ⟩ → Ω 𝓤
    F = pr₁ ℱ

\end{code}

\begin{code}

 open ScottLocaleProperties 𝓓 hl hscb pe

 family-of-compact-opens-is-inhabited : (ℱ@(F , _) : Point)
                                      → is-inhabited
                                         (underlying-order 𝓓)
                                         (Σ i ꞉ index B𝓓 , ↑ˢ[ βₖ i ] ∈ₚ F holds)
 family-of-compact-opens-is-inhabited ℱ = ∥∥-rec ∃-is-prop † γ
   where
    F : ⟨ 𝒪 σ⦅𝓓⦆ ⟩ → Ω 𝓤
    F = pr₁ ℱ

    Ⅲ : F 𝟏[ 𝒪 σ⦅𝓓⦆ ] ＝ ⊤
    Ⅲ = frame-homomorphisms-preserve-top (𝒪 σ⦅𝓓⦆) (𝒪 𝟏L) ℱ

    ζ : 𝟏[ 𝒪 σ⦅𝓓⦆ ] ∈ F
    ζ = equal-⊤-gives-holds (F 𝟏[ 𝒪 σ⦅𝓓⦆ ]) Ⅲ

    † : Σ i ꞉ index B𝓓 , B𝓓 [ i ] ＝ ⊥ᴰ → ∃ i ꞉ index B𝓓 , ↑ˢ[ βₖ i ] ∈ₚ F holds
    † (i , p) = ∣ i , equal-⊤-gives-holds (F ↑ˢ[ βₖ i ]) ※ ∣
     where
      Ⅰ = ap F (to-subtype-＝ (holds-is-prop ∘ is-scott-open) (ap (principal-filter 𝓓) p))
      Ⅱ = ap F ↑⊥-is-top

      ※ : F ↑ˢ[ βₖ i ] ＝ ⊤
      ※ = F ↑ˢ[ βₖ i ]    ＝⟨ Ⅰ ⟩
          F ↑ˢ[ ⊥ᴰ , ⊥κ ] ＝⟨ Ⅱ ⟩
          F 𝟏[ 𝒪 σ⦅𝓓⦆ ]   ＝⟨ Ⅲ ⟩
          ⊤               ∎

    γ : ∃ i ꞉ index B𝓓 , B𝓓 [ i ] ＝ ⊥ᴰ
    γ = small-compact-basis-contains-all-compact-elements 𝓓 (B𝓓 [_]) scb ⊥ᴰ ⊥κ

 closed-under-binary-upperbounds : (ℱ : Point)
                                 → is-semidirected
                                    (underlying-order 𝓓)
                                    (compact-opens-of ℱ [_])
 closed-under-binary-upperbounds ℱ (i , κᵢ) (j , κⱼ) =
  cases †₁ †₂ (dc (B𝓓 [ i ]) (B𝓓 [ j ]) (basis-is-compact i) (basis-is-compact j))
   where
    F = pr₁ ℱ

    b  = B𝓓 [ i ]
    κᵇ = basis-is-compact i
    c  = B𝓓 [ j ]
    κᶜ = basis-is-compact j

    †₁ : bounded-above 𝓓 (B𝓓 [ i ]) (B𝓓 [ j ]) holds
       → ∃ k ꞉ index (compact-opens-of ℱ)
             , (compact-opens-of ℱ [ i , κᵢ ]) ⊑⟨ 𝓓 ⟩ (compact-opens-of ℱ [ k ])
             × (compact-opens-of ℱ [ j , κⱼ ]) ⊑⟨ 𝓓 ⟩ (compact-opens-of ℱ [ k ])
    †₁ υ = ∥∥-rec ∃-is-prop †₂ 𝒷ᵈ
     where
      𝓈 : has-sup (underlying-order 𝓓) (binary-family 𝓤 b c [_])
      𝓈 = bc (binary-family 𝓤 b c) υ

      d : ⟨ 𝓓 ⟩∙
      d = pr₁ 𝓈

      p : b ⊑⟨ 𝓓 ⟩ d
      p = pr₁ (pr₂ 𝓈) (inl ⋆)

      q : c ⊑⟨ 𝓓 ⟩ d
      q = pr₁ (pr₂ 𝓈) (inr ⋆)

      κᵈ : is-compact 𝓓 d
      κᵈ = sup-is-compact b c d κᵇ κᶜ (pr₂ 𝓈)

      𝒷ᵈ : (d ∈imageₚ (B𝓓 [_])) holds
      𝒷ᵈ = small-compact-basis-contains-all-compact-elements 𝓓 (B𝓓 [_]) scb d κᵈ

      †₂ : Σ k ꞉ index B𝓓 , B𝓓 [ k ] ＝ d
         → ∃ (λ k →
                 ((compact-opens-of ℱ [ i , κᵢ ]) ⊑⟨ 𝓓 ⟩ (B𝓓 [ pr₁ k ]))
               × ((compact-opens-of ℱ [ j , κⱼ ]) ⊑⟨ 𝓓 ⟩ (B𝓓 [ pr₁ k ])))
      †₂ = {!!}

    μₘ : (↑ˢ[ b , κᵇ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ c , κᶜ ]) ∈ F
    μₘ = equal-⊤-gives-holds (F (↑ˢ[ b , κᵇ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ c , κᶜ ])) †
     where
      Ⅰ = frame-homomorphisms-preserve-meets
           (𝒪 Σ⦅𝓓⦆)
           (𝟎-𝔽𝕣𝕞 pe)
           ℱ
           ↑ˢ[ b , κᵇ ]
           ↑ˢ[ c , κᶜ ]

      Ⅱ = holds-gives-equal-⊤ pe fe (F ↑ˢ[ b , κᵇ ] ∧ₚ F ↑ˢ[ c , κᶜ ]) (κᵢ , κⱼ)

      † : F (↑ˢ[ b , κᵇ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ c , κᶜ ]) ＝ ⊤
      † = F (↑ˢ[ b , κᵇ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ c , κᶜ ]) ＝⟨ Ⅰ ⟩
          F ↑ˢ[ b , κᵇ ] ∧ₚ F ↑ˢ[ c , κᶜ ]          ＝⟨ Ⅱ ⟩
          ⊤                                         ∎

    †₂ : ¬ ((B𝓓 [ i ]) ↑[ 𝓓 ] (B𝓓 [ j ]) holds)
       → ∃ k ꞉ index (compact-opens-of ℱ)
             , (compact-opens-of ℱ [ i , κᵢ ]) ⊑⟨ 𝓓 ⟩ (compact-opens-of ℱ [ k ])
             × (compact-opens-of ℱ [ j , κⱼ ]) ⊑⟨ 𝓓 ⟩ (compact-opens-of ℱ [ k ])
    †₂ ν = 𝟘-elim (⊥-is-not-⊤ ϟ)
     where
      β : ↑ˢ[ b , κᵇ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ c , κᶜ ] ＝ 𝟎[ 𝒪 Σ⦅𝓓⦆ ]
      β = not-bounded-lemma b c κᵇ κᶜ ν

      Ⅰ = 𝟎-is-⊥ pe
      Ⅱ = {! frame-homomorphisms-preserve-bottom (𝒪 Σ⦅𝓓⦆) (𝟎-𝔽𝕣𝕞 pe) ℱ ⁻¹ !}
      Ⅲ = ap F (β ⁻¹)
      Ⅳ = holds-gives-equal-⊤ pe fe (F (↑ˢ[ b , κᵇ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ c , κᶜ ])) μₘ

      ϟ : ⊥ₚ ＝ ⊤
      ϟ = ⊥ₚ                                          ＝⟨ Ⅰ ⟩
          𝟎[ (𝟎-𝔽𝕣𝕞 pe) ]                             ＝⟨ Ⅱ ⟩
          F 𝟎[ 𝒪 Σ⦅𝓓⦆ ]                               ＝⟨ Ⅲ ⟩
          F (↑ˢ[ b , κᵇ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ c , κᶜ ])   ＝⟨ Ⅳ ⟩
          ⊤                                           ∎

 family-of-compact-opens-is-directed : (ℱ : Point)
                                     → is-directed
                                        (underlying-order 𝓓)
                                        (compact-opens-of ℱ [_])
 family-of-compact-opens-is-directed ℱ = family-of-compact-opens-is-inhabited ℱ
                                       , closed-under-binary-upperbounds ℱ

\end{code}
