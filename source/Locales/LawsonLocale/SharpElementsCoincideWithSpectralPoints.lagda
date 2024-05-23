--------------------------------------------------------------------------------
title:          Equivalence of sharp elements with spectral points
author:         Ayberk Tosun
date-started:   2024-05-22
--------------------------------------------------------------------------------

The formalization of a proof.

\begin{code}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

module Locales.LawsonLocale.SharpElementsCoincideWithSpectralPoints
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
open import DomainTheory.BasesAndContinuity.CompactBasis pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤
open import DomainTheory.BasesAndContinuity.ScottDomain pt fe 𝓤
open import DomainTheory.Basics.Dcpo pt fe 𝓤 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Basics.WayBelow pt fe 𝓤
open import DomainTheory.Topology.ScottTopology pt fe 𝓤
open import DomainTheory.Topology.ScottTopologyProperties pt fe 𝓤
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.Frame pt fe
open import Locales.InitialFrame pt fe hiding (_⊑_)
open import Locales.LawsonLocale.CompactElementsOfPoint 𝓤 fe pe pt sr
open import Locales.ScottLocale.Definition pt fe 𝓤
open import Locales.ScottLocale.Properties pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfScottDomains pt fe sr 𝓤
open import Locales.Spectrality.SpectralMap pt fe
open import Locales.Compactness pt fe hiding (is-compact)
open import Locales.TerminalLocale.Properties pt fe sr
open import NotionsOfDecidability.SemiDecidable fe pe pt
open import Slice.Family
open import UF.Logic
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier

open AllCombinators pt fe
open DefinitionOfScottDomain
open PropositionalTruncation pt

\end{code}

\section{Preliminaries}

We define a version of the predicate `is-compact` that is packaged up with the
proof that it is a proposition.

\begin{code}

is-compactₚ : (𝓓 : DCPO {𝓤 ⁺} {𝓤}) → ⟨ 𝓓 ⟩∙ → Ω (𝓤 ⁺)
is-compactₚ 𝓓 x = is-compact 𝓓 x , being-compact-is-prop 𝓓 x

\end{code}

Similarly, we define a version of the predicate `is-decidable` that is packaged
up with the proof that it is a proposition.

\begin{code}

is-decidableₚ : (P : Ω 𝓤) → Ω 𝓤
is-decidableₚ P =
 is-decidable (P holds) , decidability-of-prop-is-prop fe (holds-is-prop P)

\end{code}

\begin{code}

module ResultOnSharpElements
        (𝓓    : DCPO {𝓤 ⁺} {𝓤})
        (hl   : has-least (underlying-order 𝓓))
        (sd   : is-scott-domain 𝓓 holds)
        (dc   : decidability-condition 𝓓)
       where

 open Construction 𝓓 ua hl sd dc
 open DefinitionOfBoundedCompleteness hiding (_⊑_)

\end{code}

We define a version of the order `_⊑_` packaged up with the proof that it
is proposition-valued.

\begin{code}

 𝒷₀ : has-unspecified-small-compact-basis 𝓓
 𝒷₀ = pr₁ sd

 bc : DefinitionOfBoundedCompleteness.bounded-complete 𝓓 holds
 bc = pr₂ sd

 hscb : has-specified-small-compact-basis 𝓓
 hscb = specified-small-compact-basis-has-split-support ua sr 𝓓 𝒷₀

 𝕒 : structurally-algebraic 𝓓
 𝕒 = structurally-algebraic-if-specified-small-compact-basis 𝓓 hscb

 open SpectralScottLocaleConstruction 𝓓 hl hscb dc bc pe hiding (scb)
 open structurally-algebraic
 open is-small-compact-basis scb

 κ : (b : B) → is-compact 𝓓 (β b)
 κ = basis-is-compact

 σ⦅𝓓⦆ : Locale (𝓤 ⁺) 𝓤 𝓤
 σ⦅𝓓⦆ = Σ[𝓓]

 _⊑_ : ⟨ 𝓓 ⟩∙ → ⟨ 𝓓 ⟩∙ → Ω 𝓤
 x ⊑ y = (x ⊑⟨ 𝓓 ⟩ y) , prop-valuedness 𝓓 x y

\end{code}

We first define what it means for an element to be sharp.

\begin{code}

 is-sharp : ⟨ 𝓓 ⟩∙ → Ω (𝓤 ⁺)
 is-sharp x = Ɐ c ꞉ ⟨ 𝓓 ⟩∙ , is-compactₚ 𝓓 c ⇒ is-decidableₚ (c ⊑ x)

\end{code}

This definition of the notion of sharpness is a predicate with large truth
values as it quantifier over the compact opens. Because we are working with an
algebraic dcpo, however, we could define a small version.

\begin{code}

 is-sharp⁻ : ⟨ 𝓓 ⟩∙ → Ω 𝓤
 is-sharp⁻ x = Ɐ i ꞉ B , is-decidableₚ (β i ⊑ x)

\end{code}

\begin{code}

 sharp-implies-sharp⁻ : (Ɐ x ꞉ ⟨ 𝓓 ⟩∙ , is-sharp x ⇒ is-sharp⁻ x) holds
 sharp-implies-sharp⁻ x 𝕤 i = 𝕤 (β i) (κ i)

\end{code}

\begin{code}

 sharp⁻-implies-sharp : (Ɐ x ꞉ ⟨ 𝓓 ⟩∙ , is-sharp⁻ x ⇒ is-sharp x) holds
 sharp⁻-implies-sharp x 𝕤 c χ =
  ∥∥-rec (holds-is-prop (is-decidableₚ (c ⊑ x))) † μ
   where
    μ : ∃ i ꞉ B , β i ＝ c
    μ = small-compact-basis-contains-all-compact-elements 𝓓 β scb c χ

    † : Σ i ꞉ B , β i ＝ c → is-decidableₚ (c ⊑ x) holds
    † (i , p) = transport (λ - → is-decidableₚ (- ⊑ x) holds) p (𝕤 i)

\end{code}

\begin{code}

 ♯𝓓 : 𝓤 ⁺  ̇
 ♯𝓓 = Σ x ꞉ ⟨ 𝓓 ⟩∙ , is-sharp x holds

\end{code}

\begin{code}

 sharp-is-equivalent-to-sharp⁻ : (x : ⟨ 𝓓 ⟩∙) → (is-sharp x ⇔ is-sharp⁻ x) holds
 sharp-is-equivalent-to-sharp⁻ x =
  sharp-implies-sharp⁻ x , sharp⁻-implies-sharp x

\end{code}

\begin{code}

 open Preliminaries
 open Locale
 open DefnOfScottTopology 𝓓 𝓤

\end{code}

\begin{code}

 pt₀[_] : ⟨ 𝓓 ⟩∙ → ⟨ 𝒪 σ⦅𝓓⦆ ⟩ → Ω 𝓤
 pt₀[_] x U = x ∈ₛ U

\end{code}

\begin{code}

 open FrameHomomorphisms

 pt[_] : ♯𝓓 → Point σ⦅𝓓⦆
 pt[_] 𝓍@(x , 𝕤) = pt₀[ x ] , †
  where
   †₂ : preserves-binary-meets (𝒪 σ⦅𝓓⦆) (𝟎-𝔽𝕣𝕞 pe) pt₀[ x ] holds
   †₂ x y = refl

   †₃ : preserves-joins (𝒪 σ⦅𝓓⦆) (𝟎-𝔽𝕣𝕞 pe) pt₀[ x ] holds
   †₃ = {!!}

   foo : preserves-joins′ (𝒪 σ⦅𝓓⦆) (𝟎-𝔽𝕣𝕞 pe) pt₀[ x ] holds
   foo S = refl

   † : is-a-frame-homomorphism (𝒪 σ⦅𝓓⦆) (𝟎-𝔽𝕣𝕞 pe) pt₀[ x ] holds
   † = refl , (λ _ _ → refl) , †₃

\end{code}

Given any sharp element `𝓍`, the point `pt 𝓍` is a spectral map.

\begin{code}

 open PropertiesAlgebraic 𝓓 𝕒
 open Properties 𝓓

 pt-is-spectral : (𝓍 : ♯𝓓) → is-spectral-map σ⦅𝓓⦆ (𝟏Loc pe) pt[ 𝓍 ] holds
 pt-is-spectral 𝓍@(x , _) (K , σ) 𝕜 = decidable-implies-compact pe P {!!}
  where
   P : Ω 𝓤
   P = pt₀[ x ] (K , σ)

   foo : pt₀[ x ] (⋁[ 𝒪 σ⦅𝓓⦆ ] ⁅ ↑ˢ[ β i , κ i ] ∣ (i , _) ∶ (Σ i ꞉ B , K (β i) holds) ⁆)
       ＝ ⋁[ 𝟎-𝔽𝕣𝕞 pe ] ⁅  pt₀[ x ] ↑ˢ[ β i , κ i ]  ∣ (i , _) ∶ (Σ i ꞉ B , K (β i) holds) ⁆
   foo = refl

   goal : is-compact-open (𝟏Loc pe) (Ǝₚ (i , _) ꞉ (Σ i ꞉ B , K (β i) holds) , pt₀[ x ] ↑ˢ[ β i , κ i ]) holds
   goal S δ p = {!!}
    where
     baz : {!!} → ∃ i ꞉ index S , (S [ i ]) holds
     baz = p
    -- frame-homomorphisms-preserve-all-joins′
    --  (𝒪 σ⦅𝓓⦆)
    --  (𝟎-𝔽𝕣𝕞 pe)
    --  pt[ 𝓍 ]
    --  ⁅ ↑ˢ[ β i , κ i ] ∣ (i , _) ∶ (Σ i ꞉ B , K (β i) holds) ⁆
  -- ∥∥-rec ∃-is-prop goal (bar (♠ {!!}))
  --  where
  --   ♠ : join-of-compact-opens K x holds → K x holds
  --   ♠ = characterization-of-scott-opens₂ K σ x

  --   bar : K x holds → ∃ i ꞉ index S , (S [ i ]) holds
  --   bar = p

  --   goal : (Σ i ꞉ index S , (S [ i ]) holds)
  --        → ∃ i ꞉ index S , (K x ⇒ S [ i ]) holds
  --   goal (i , p) = ∣ i , (λ _ → p) ∣

\end{code}

\begin{code}

 sharp₀ : Point σ⦅𝓓⦆ → ⟨ 𝓓 ⟩∙
 sharp₀ F = ⋁ (𝒦-in-point F , δ)
  where
   δ : is-Directed 𝓓 (𝒦-in-point F [_])
   δ = 𝒦-in-point-is-directed F

\end{code}
