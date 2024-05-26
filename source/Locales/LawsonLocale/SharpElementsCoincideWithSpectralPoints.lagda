---
title:          Equivalence of sharp elements with spectral points
author:         Ayberk Tosun
date-started:   2024-05-22
---

The formalization of a proof.

\begin{code}

{--# OPTIONS --safe --without-K --lossy-unification #--}

open import MLTT.Spartan
open import MLTT.List hiding ([_])
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
open import Locales.Compactness pt fe hiding (is-compact)
open import Locales.Clopen pt fe sr
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.Frame pt fe
open import Locales.InitialFrame pt fe hiding (_⊑_)
open import Locales.LawsonLocale.CompactElementsOfPoint 𝓤 fe pe pt sr
open import Locales.CompactRegular pt fe using (clopens-are-compact-in-compact-frames)
open import Locales.ScottLocale.Definition pt fe 𝓤
open import Locales.ScottLocale.Properties pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfScottDomains pt fe sr 𝓤
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralMap pt fe
open import Locales.TerminalLocale.Properties pt fe sr
open import NotionsOfDecidability.Decidable
open import NotionsOfDecidability.SemiDecidable fe pe pt
open import Slice.Family
open import UF.Logic
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier

open AllCombinators pt fe
open DefinitionOfScottDomain
open PropositionalTruncation pt hiding (_∨_)

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

 open SpectralScottLocaleConstruction₂ 𝓓 ua hl sd dc pe
 open SpectralScottLocaleConstruction 𝓓 hl hscb dc bc pe hiding (scb; σᴰ)
 open ScottLocaleProperties 𝓓 hl hscb pe renaming (⊤-is-compact to σ⦅𝓓⦆-is-compact)

 open structurally-algebraic
 open is-small-compact-basis scb
 open Locale

 σᴰ : spectralᴰ σ⦅𝓓⦆
 σᴰ = scott-locale-spectralᴰ

 basis : Fam 𝓤 ⟨ 𝒪 σ⦅𝓓⦆ ⟩
 basis = basisₛ σ⦅𝓓⦆ σᴰ

 Bσ : 𝓤  ̇
 Bσ = index basis

 βσ : Bσ → ⟨ 𝒪 σ⦅𝓓⦆ ⟩
 βσ = basis [_]

 κσ : (i : Bσ) → is-compact-open σ⦅𝓓⦆ (βσ i) holds
 κσ = basisₛ-consists-of-compact-opens σ⦅𝓓⦆ σᴰ

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
 is-sharp⁻ x = Ɐ i ꞉ index B𝓓 , is-decidableₚ ((B𝓓 [ i ]) ⊑ x)

\end{code}

\begin{code}

 sharp-implies-sharp⁻ : (Ɐ x ꞉ ⟨ 𝓓 ⟩∙ , is-sharp x ⇒ is-sharp⁻ x) holds
 sharp-implies-sharp⁻ x 𝕤 i = 𝕤 (B𝓓 [ i ]) (basis-is-compact i)

\end{code}

\begin{code}

 sharp⁻-implies-sharp : (Ɐ x ꞉ ⟨ 𝓓 ⟩∙ , is-sharp⁻ x ⇒ is-sharp x) holds
 sharp⁻-implies-sharp x 𝕤 c χ =
  ∥∥-rec (holds-is-prop (is-decidableₚ (c ⊑ x))) † μ
   where
    μ : ∃ i ꞉ index B𝓓 , B𝓓 [ i ] ＝ c
    μ = small-compact-basis-contains-all-compact-elements 𝓓 (B𝓓 [_]) scb c χ

    † : Σ i ꞉ index B𝓓 , B𝓓 [ i ] ＝ c → is-decidableₚ (c ⊑ x) holds
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
 open FrameHomomorphismProperties (𝒪 σ⦅𝓓⦆) (𝟎-𝔽𝕣𝕞 pe)

 pt[_] : ♯𝓓 → Point σ⦅𝓓⦆
 pt[_] 𝓍@(x , 𝕤) = pt₀[ x ] , †
  where
   ‡ : preserves-joins (𝒪 σ⦅𝓓⦆) (𝟎-𝔽𝕣𝕞 pe) pt₀[ x ] holds
   ‡ S = (⋁[ 𝟎-𝔽𝕣𝕞 pe ]-upper ⁅ pt₀[ x ] y ∣ y ε S ⁆) , goal
    where
     open Joins _⇒_

     goal : ((u , _) : upper-bound ⁅ pt₀[ x ] y ∣ y ε S ⁆)
          → (pt₀[ x ] (⋁[ 𝒪 σ⦅𝓓⦆ ] S) ⇒ u) holds
     goal (u , a) p = ⋁[ 𝟎-𝔽𝕣𝕞 pe ]-least ⁅ pt₀[ x ] y ∣ y ε S ⁆ (u , a) p

   † : is-a-frame-homomorphism (𝒪 σ⦅𝓓⦆) (𝟎-𝔽𝕣𝕞 pe) pt₀[ x ] holds
   † = refl , (λ _ _ → refl) , ‡

\end{code}

\begin{code}

 -- TODO: has this been written down somewhere?

 ∨-preserves-decidability : (P Q : Ω 𝓤)
                          → is-decidableₚ P holds
                          → is-decidableₚ Q holds
                          → is-decidableₚ (P ∨ Q) holds
 ∨-preserves-decidability P Q φ ψ =
  cases case₁ case₂ (+-preserves-decidability φ ψ)
   where
    case₁ : (P holds) + (Q holds) → is-decidableₚ (P ∨ Q) holds
    case₁ (inl p) = inl ∣ inl p ∣
    case₁ (inr q) = inl ∣ inr q ∣

    case₂ : ¬ (P holds + Q holds) → is-decidableₚ (P ∨ Q) holds
    case₂ = inr ∘ ∥∥-rec 𝟘-is-prop

\end{code}

For any sharp element `𝓍` and any compact Scott open `𝒦`, `𝓍 ∈ 𝒦` is a decidable
proposition.

\begin{code}

 open BottomLemma 𝓓 𝕒 hl
 open Properties 𝓓

\end{code}

We define the following predicate expressing that an element `x` has decidable
membership in compact Scott opens.

\begin{code}

 admits-decidable-membership-in-compact-scott-opens : ⟨ 𝓓 ⟩∙ → Ω (𝓤 ⁺)
 admits-decidable-membership-in-compact-scott-opens x =
  Ɐ 𝒦 ꞉ ⟨ 𝒪 σ⦅𝓓⦆ ⟩ , is-compact-open σ⦅𝓓⦆ 𝒦 ⇒ is-decidableₚ (x ∈ₛ 𝒦)

 admits-decidable-membership-in-scott-clopens : ⟨ 𝓓 ⟩∙ → Ω (𝓤 ⁺)
 admits-decidable-membership-in-scott-clopens x =
  Ɐ 𝒦 ꞉ ⟨ 𝒪 σ⦅𝓓⦆ ⟩ , is-clopen (𝒪 σ⦅𝓓⦆) 𝒦 ⇒ is-decidableₚ (x ∈ₛ 𝒦)

\end{code}

Every sharp element satisfies this property.

\begin{code}

 sharp-implies-admits-decidable-membership-in-compact-scott-opens
  : (x : ⟨ 𝓓 ⟩∙)
  → (is-sharp x ⇒ admits-decidable-membership-in-compact-scott-opens x) holds
 sharp-implies-admits-decidable-membership-in-compact-scott-opens x 𝓈𝒽 𝒦 𝕜 =
  ∥∥-rec (holds-is-prop (is-decidableₚ (x ∈ₛ 𝒦))) † ♢
   where
    ♢ : is-basic σ⦅𝓓⦆ 𝒦 (spectralᴰ-implies-directed-basisᴰ σ⦅𝓓⦆ σᴰ) holds
    ♢ = compact-opens-are-basic
         σ⦅𝓓⦆
         (spectralᴰ-implies-directed-basisᴰ σ⦅𝓓⦆ σᴰ)
         𝒦
         𝕜

    quux : βσ [] ＝ 𝟎[ 𝒪 σ⦅𝓓⦆ ]
    quux = 𝜸-equal-to-𝜸₁ []

    lemma : (xs : List (index B𝓓)) → is-decidableₚ (x ∈ₛ βσ xs) holds
    lemma []       = inr 𝟘-elim
    lemma (i ∷ is) = ∨-preserves-decidability (x ∈ₛ ↑ˢ[ βₖ i ]) (x ∈ₛ 𝜸 is) †₁ †₂
     where
      †₁ : is-decidableₚ (x ∈ₛ ↑ˢ[ βₖ i ]) holds
      †₁ = 𝓈𝒽 (β i) (basis-is-compact i)

      †₂ : is-decidableₚ (x ∈ₛ 𝜸 is) holds
      †₂ = lemma is

    ‡ : (xs : List (index B𝓓)) → βσ xs ＝ 𝒦 → is-decidableₚ (x ∈ₛ 𝒦) holds
    ‡ xs p = transport (λ - → is-decidableₚ (x ∈ₛ -) holds) p (lemma xs)

    † : Σ xs ꞉ List (index B𝓓) , βσ xs ＝ 𝒦 → is-decidableₚ (x ∈ₛ 𝒦) holds
    † (xs , q) = ‡ xs q

\end{code}

\begin{code}

 admits-decidable-membership-in-compact-scott-opens-implies-is-sharp
  : (x : ⟨ 𝓓 ⟩∙)
  → admits-decidable-membership-in-compact-scott-opens x holds
  → is-sharp x holds
 admits-decidable-membership-in-compact-scott-opens-implies-is-sharp x φ c 𝕜 =
  φ ↑ˢ[ (c , 𝕜) ] (principal-filter-is-compact₀ c 𝕜)

\end{code}

\begin{code}

 admits-decidable-membership-in-scott-clopens-implies-is-sharp
  : (x : ⟨ 𝓓 ⟩∙)
  → is-sharp x holds
  → admits-decidable-membership-in-scott-clopens x holds
 admits-decidable-membership-in-scott-clopens-implies-is-sharp x 𝓈𝒽 K χ =
  ψ K κ
   where
    ψ : admits-decidable-membership-in-compact-scott-opens x holds
    ψ = sharp-implies-admits-decidable-membership-in-compact-scott-opens x 𝓈𝒽

    κ : is-compact-open σ⦅𝓓⦆ K holds
    κ = clopens-are-compact-in-compact-frames
         (𝒪 σ⦅𝓓⦆)
         σ⦅𝓓⦆-is-compact
         K
         χ


\end{code}

\begin{code}

 characterization-of-sharp-elements
  : (x : ⟨ 𝓓 ⟩∙)
  → (admits-decidable-membership-in-compact-scott-opens x ⇔ is-sharp x) holds
 characterization-of-sharp-elements x = † , ‡
  where
   † = admits-decidable-membership-in-compact-scott-opens-implies-is-sharp x
   ‡ = sharp-implies-admits-decidable-membership-in-compact-scott-opens x

\end{code}

Given any sharp element `𝓍`, the point `pt 𝓍` is a spectral map.

\begin{code}

 pt-is-spectral : (𝓍 : ♯𝓓) → is-spectral-map σ⦅𝓓⦆ (𝟏Loc pe) pt[ 𝓍 ] holds
 pt-is-spectral 𝓍@(x , 𝓈𝒽) 𝒦@(K , σ) 𝕜 = decidable-implies-compact pe (x ∈ₛ 𝒦) †
  where
   † : is-decidableₚ (x ∈ₛ (K , σ)) holds
   † = sharp-implies-admits-decidable-membership-in-compact-scott-opens x 𝓈𝒽 𝒦 𝕜

\end{code}

\begin{code}

 sharp₀ : Point σ⦅𝓓⦆ → ⟨ 𝓓 ⟩∙
 sharp₀ F = ⋁ (𝒦-in-point F , δ)
  where
   δ : is-Directed 𝓓 (𝒦-in-point F [_])
   δ = 𝒦-in-point-is-directed F

\end{code}

\begin{code}

 lemma-6 : (ℱ@(F , _) : Point σ⦅𝓓⦆) (c : ⟨ 𝓓 ⟩∙) (𝕜 : is-compact 𝓓 c)
         → c ⊑⟨ 𝓓 ⟩ {!⋁ (𝒦-in-point ℱ , δ) !} → F ↑ˢ[ c , 𝕜 ] holds
 lemma-6 F c 𝕜 p = {!!}

 sharp₀-gives-sharp-elements : (F : Point σ⦅𝓓⦆) → is-sharp (sharp₀ F) holds
 sharp₀-gives-sharp-elements F c 𝕜 = {!!}

 sharp : Point σ⦅𝓓⦆ → ♯𝓓
 sharp F = sharp₀ F , sharp₀-gives-sharp-elements F

\end{code}
