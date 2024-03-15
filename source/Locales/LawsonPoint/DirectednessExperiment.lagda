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
open import DomainTheory.Basics.WayBelow pt fe 𝓤
open import DomainTheory.Basics.Pointed pt fe 𝓤
open import DomainTheory.Topology.ScottTopology pt fe 𝓤
open import DomainTheory.Topology.ScottTopologyProperties pt fe 𝓤
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
open import MLTT.Fin hiding (𝟎; 𝟏)
open import MLTT.List hiding ([_])
open import Slice.Family
open import UF.Logic
open import UF.Powerset
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.Univalence

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)
open Locale
open PropositionalTruncation pt hiding (_∨_)

\end{code}

\begin{code}

module Preliminaries (X : Locale (𝓤 ⁺) 𝓤 𝓤) where

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
 open DefnOfScottTopology 𝓓 𝓤
 open Properties 𝓓

 open Preliminaries σ⦅𝓓⦆

 B𝓓 : Fam 𝓤 ⟨ 𝓓 ⟩∙
 B𝓓 = index-of-compact-basis 𝓓 hscb , family-of-compact-elements 𝓓 hscb

 scb : is-small-compact-basis 𝓓 (family-of-compact-elements 𝓓 hscb)
 scb = small-compact-basis 𝓓 hscb

 open is-small-compact-basis scb

 open BottomLemma 𝓓 𝕒 hl

 κ : (i : index B𝓓) → is-compact 𝓓 (B𝓓 [ i ])
 κ i = basis-is-compact i

 compact-opens-of : Point → Fam 𝓤 ⟨ 𝓓 ⟩∙
 compact-opens-of ℱ = ⁅ B𝓓 [ c ] ∣ (c , _) ∶ Σ i ꞉ index B𝓓 , ↑ˢ[ (B𝓓 [ i ] , κ i) ] ∈ₚ F holds ⁆
  where
   F : ⟨ 𝒪 σ⦅𝓓⦆ ⟩ → Ω 𝓤
   F = pr₁ ℱ

\end{code}

\begin{code}

 open ScottLocaleProperties 𝓓 hl hscb pe

 family-of-compact-opens-is-inhabited : (ℱ@(F , _) : Point)
                                      → is-inhabited
                                         (underlying-order 𝓓)
                                         (Σ i ꞉ index B𝓓 , ↑ˢ[ (B𝓓 [ i ] , κ i) ] ∈ₚ F holds)
 family-of-compact-opens-is-inhabited ℱ = ∥∥-rec ∃-is-prop † γ
   where
    F : ⟨ 𝒪 σ⦅𝓓⦆ ⟩ → Ω 𝓤
    F = pr₁ ℱ

    foo : F 𝟏[ 𝒪 σ⦅𝓓⦆ ] ＝ ⊤
    foo = frame-homomorphisms-preserve-top (𝒪 σ⦅𝓓⦆) (𝒪 𝟏L) ℱ

    ζ : 𝟏[ 𝒪 σ⦅𝓓⦆ ] ∈ F
    ζ = equal-⊤-gives-holds (F 𝟏[ 𝒪 σ⦅𝓓⦆ ]) foo

    † : Σ i ꞉ index B𝓓 , B𝓓 [ i ] ＝ ⊥ᴰ → ∃ i ꞉ index B𝓓 , ↑ˢ[ (B𝓓 [ i ] , κ i) ] ∈ₚ F holds
    † (i , p) = ∣ i , equal-⊤-gives-holds (F ↑ˢ[ (B𝓓 [ i ] , κ i) ]) ※ ∣
     where
      ※ : F ↑ˢ[ B𝓓 [ i ] , κ i ] ＝ ⊤
      ※ = F ↑ˢ[ B𝓓 [ i ] , κ i ]   ＝⟨ ap F (to-subtype-＝ (holds-is-prop ∘ is-scott-open) (ap (principal-filter 𝓓) p)) ⟩
          F ↑ˢ[ ⊥ᴰ , ⊥κ ]          ＝⟨ ap F ↑⊥-is-top ⟩
          F 𝟏[ 𝒪 σ⦅𝓓⦆ ]            ＝⟨ foo  ⟩
          ⊤                        ∎

    γ : ∃ i ꞉ index B𝓓 , B𝓓 [ i ] ＝ ⊥ᴰ
    γ = small-compact-basis-contains-all-compact-elements 𝓓 (B𝓓 [_]) scb ⊥ᴰ ⊥κ

 family-of-compact-opens-is-directed : (ℱ : Point)
                                     → is-directed
                                        (underlying-order 𝓓)
                                        (compact-opens-of ℱ [_])
 family-of-compact-opens-is-directed ℱ = family-of-compact-opens-is-inhabited ℱ
                                       , {!!}

\end{code}
