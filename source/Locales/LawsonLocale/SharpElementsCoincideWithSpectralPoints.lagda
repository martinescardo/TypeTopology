---
title:          Equivalence of sharp elements with spectral points
author:         Ayberk Tosun
date-started:   2024-05-22
---

The formalization of a proof.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

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
open import Locales.Clopen pt fe sr
open import Locales.CompactRegular pt fe using (clopens-are-compact-in-compact-frames)
open import Locales.Compactness pt fe hiding (is-compact)
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.Frame pt fe
open import Locales.InitialFrame pt fe hiding (_⊑_)
open import Locales.LawsonLocale.CompactElementsOfPoint 𝓤 fe pe pt sr
open import Locales.Point.Definition pt fe
open import Locales.Point.SpectralPoint-Definition pt fe
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
open import UF.Equiv
open import UF.Logic
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier renaming (⊥ to ⊥ₚ)

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

 abstract
  to-sharp-＝ : (𝓍 𝓎 : ♯𝓓) → pr₁ 𝓍 ＝ pr₁ 𝓎 → 𝓍 ＝ 𝓎
  to-sharp-＝ 𝓍 𝓎 = to-subtype-＝ (holds-is-prop ∘ is-sharp)

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

 open Notion-Of-Spectral-Point pe

 𝓅𝓉[_] : ♯𝓓 → Spectral-Point σ⦅𝓓⦆
 𝓅𝓉[_] 𝓍 = to-spectral-point σ⦅𝓓⦆ ℱ
  where
   ℱ : Spectral-Map (𝟏Loc pe) σ⦅𝓓⦆
   ℱ = pt[ 𝓍 ] , pt-is-spectral 𝓍

\end{code}

\begin{code}

 sharp₀ : Point σ⦅𝓓⦆ → ⟨ 𝓓 ⟩∙
 sharp₀ ℱ = ∐ 𝓓 (𝒦-in-point-is-directed ℱ)

 lemma-6-⇒ : (ℱ@(F , _) : Point σ⦅𝓓⦆) (c : ⟨ 𝓓 ⟩∙) (𝕜 : is-compact 𝓓 c)
         → c ⊑⟨ 𝓓 ⟩ sharp₀ ℱ → F ↑ˢ[ c , 𝕜 ] holds
 lemma-6-⇒ ℱ@(F , 𝒽) c 𝕜 p =
  ∥∥-rec (holds-is-prop (F ↑ˢ[ c , 𝕜 ])) † γ
   where
    open 𝒪ₛᴿ (to-𝒪ₛᴿ ↑ˢ[ c , 𝕜 ])

    γ : ∃ (i , _) ꞉ (index (𝒦-in-point ℱ)) , c ⊑⟨ 𝓓 ⟩ (B𝓓 [ i ])
    γ = pred-is-inaccessible-by-dir-joins (𝒦-in-point↑ ℱ) p

    † : Σ (i , _) ꞉ (index (𝒦-in-point ℱ)) , c ⊑⟨ 𝓓 ⟩ (B𝓓 [ i ])
      → F ↑ˢ[ c , 𝕜 ] holds
    † ((i , p) , φ) =
     frame-morphisms-are-monotonic F 𝒽 (↑ˢ[ βₖ i ] , ↑ˢ[ c , 𝕜 ]) ‡ p
      where
       ‡ : (↑ˢ[ βₖ i ] ≤[ poset-of (𝒪 σ⦅𝓓⦆) ] ↑ˢ[ c , 𝕜 ]) holds
       ‡ =
        principal-filter-is-antitone c (B𝓓 [ i ]) φ 𝕜 (basis-is-compact i)

 lemma-6-⇐ : (ℱ@(F , _) : Point σ⦅𝓓⦆) (c : ⟨ 𝓓 ⟩∙) (𝕜 : is-compact 𝓓 c)
           → F ↑ˢ[ c , 𝕜 ] holds → c ⊑⟨ 𝓓 ⟩ sharp₀ ℱ
 lemma-6-⇐ ℱ@(F , ψ) c 𝕜 χ =
  ∥∥-rec (prop-valuedness 𝓓 c (⋁ 𝒦-in-point↑ ℱ)) † γ
   where
    γ : ∃ i ꞉ index B𝓓 , B𝓓 [ i ] ＝ c
    γ = small-compact-basis-contains-all-compact-elements 𝓓 (B𝓓 [_]) scb c 𝕜

    † : Σ i ꞉ index B𝓓 , B𝓓 [ i ] ＝ c → c ⊑⟨ 𝓓 ⟩ (⋁ 𝒦-in-point↑ ℱ)
    † (i , p) = transport (λ - → - ⊑⟨ 𝓓 ⟩ (⋁ 𝒦-in-point↑ ℱ)) p ‡
     where
      q : ↑ˢ[ βₖ i ] ＝ ↑ˢ[ c , 𝕜 ]
      q = ap ↑ˢ[_] (to-subtype-＝ (holds-is-prop ∘ is-compactₚ 𝓓) p)

      μ : F ↑ˢ[ βₖ i ] holds
      μ = transport (λ - → F - holds) (q ⁻¹) χ

      ‡ : (B𝓓 [ i ]) ⊑⟨ 𝓓 ⟩ (⋁ 𝒦-in-point↑ ℱ)
      ‡ = ⋁-is-upperbound (𝒦-in-point↑ ℱ) (i , μ)

 sharp₀-gives-sharp-elements : (F : Point σ⦅𝓓⦆)
                             → is-spectral-map σ⦅𝓓⦆ (𝟏Loc pe) F holds
                             → is-sharp (sharp₀ F) holds
 sharp₀-gives-sharp-elements ℱ@(F , _) σ c 𝕜 = cases case₁ case₂ γ
  where
   φ : is-compact-open (𝟏Loc pe) (F ↑ˢ[ c , 𝕜 ]) holds
   φ = σ ↑ˢ[ c , 𝕜 ] (principal-filter-is-compact₀ c 𝕜 )

   γ : is-decidableₚ (F ↑ˢ[ c , 𝕜 ]) holds
   γ = compact-implies-boolean pe (F ↑ˢ[ c , 𝕜 ]) φ

   case₁ : F ↑ˢ[ c , 𝕜 ] holds → is-decidableₚ (c ⊑ sharp₀ ℱ) holds
   case₁ = inl ∘ lemma-6-⇐ ℱ c 𝕜

   case₂ : ¬ (F ↑ˢ[ c , 𝕜 ] holds) → is-decidableₚ (c ⊑ sharp₀ ℱ) holds
   case₂ χ = inr λ q → χ (lemma-6-⇒ ℱ c 𝕜 q)

\end{code}

\begin{code}

 sharp : Spectral-Point σ⦅𝓓⦆ → ♯𝓓
 sharp ℱ = sharp₀ F· , sharp₀-gives-sharp-elements F· σ
  where
   open Spectral-Point σ⦅𝓓⦆ ℱ
    renaming (point-fn to F; point to F·; point-preserves-compactness to σ)

\end{code}

\begin{code}

 ⦅_⦆ : ♯𝓓 → ⟨ 𝓓 ⟩∙
 ⦅_⦆ (x , _) = x

\end{code}

We now proceed to prove that the type of sharp elements is equivalent to the
type of spectral points.

\begin{code}

 abstract
  lemma₁ : (x : ⟨ 𝓓 ⟩∙) (𝕤 : is-sharp x holds) (c : ⟨ 𝓓 ⟩∙)
         → is-compact 𝓓 c
         → c ⊑⟨ 𝓓 ⟩ x
         → c ⊑⟨ 𝓓 ⟩ (⋁ 𝒦-in-point↑ pt[ (x , 𝕤) ])
  lemma₁ x 𝕤 c κ p = ∥∥-rec (prop-valuedness 𝓓 c (sharp₀ pt[ x , 𝕤 ])) † γ
   where
    † : (Σ i ꞉ index B𝓓 , B𝓓 [ i ] ＝ c) → c ⊑⟨ 𝓓 ⟩ sharp₀ pt[ x , 𝕤 ]
    † (i , q) = transport (λ - → underlying-order 𝓓 - (sharp₀ pt[ x , 𝕤 ])) q ‡
     where
      r : (B𝓓 [ i ]) ⊑⟨ 𝓓 ⟩ x
      r = transport (λ - → - ⊑⟨ 𝓓 ⟩ x) (q ⁻¹) p

      ‡ : (B𝓓 [ i ]) ⊑⟨ 𝓓 ⟩ sharp₀ pt[ x , 𝕤 ]
      ‡ = sup-is-upperbound (underlying-order 𝓓)
           (⋁-is-sup (𝒦-in-point↑ pt[ x , 𝕤 ])) (i , r)

    γ : ∃ i ꞉ index B𝓓 , B𝓓 [ i ] ＝ c
    γ = small-compact-basis-contains-all-compact-elements 𝓓 (B𝓓 [_]) scb c κ

 lemma₃ : (x : ⟨ 𝓓 ⟩∙) (𝕤 : is-sharp x holds) (c : ⟨ 𝓓 ⟩∙)
        → is-compact 𝓓 c
        → ∃ i ꞉ (index (𝒦-in-point pt[ (x , 𝕤) ])) , c ＝ 𝒦-in-point pt[ (x , 𝕤) ] [ i ]
        → c ⊑⟨ 𝓓 ⟩ x
 lemma₃ x 𝕤 c κ = ∥∥-rec (prop-valuedness 𝓓 c x) †
  where
   † : Σ i ꞉ (index (𝒦-in-point pt[ (x , 𝕤) ])) , c ＝ 𝒦-in-point pt[ x , 𝕤 ] [ i ]
     → c ⊑⟨ 𝓓 ⟩ x
   † ((i , foo) , r) = transport (λ - → - ⊑⟨ 𝓓 ⟩ x) (r ⁻¹) foo

 abstract
  lemma₄ : (x : ⟨ 𝓓 ⟩∙) (𝕤 : is-sharp x holds)
         → ∐ 𝓓 (↓ᴮₛ-is-directed x) ＝ ∐ 𝓓 (𝒦-in-point-is-directed pt[ (x , 𝕤) ])
  lemma₄ x 𝕤 =
   antisymmetry 𝓓 (∐ 𝓓 (↓ᴮₛ-is-directed x)) (⋁ 𝒦-in-point↑ pt[ (x , 𝕤) ]) † ‡
    where
     abstract
      † : (∐ 𝓓 (↓ᴮₛ-is-directed x)) ⊑⟨ 𝓓 ⟩ (⋁ 𝒦-in-point↑ pt[ (x , 𝕤) ])
      † = ∐-is-lowerbound-of-upperbounds
           𝓓
           (↓ᴮₛ-is-directed x)
           (⋁ 𝒦-in-point↑ pt[ x , 𝕤 ])
           goal
            where
             goal : (i : ↓ᴮₛ x) →
                     underlying-order 𝓓 (↓-inclusionₛ x i) (⋁ 𝒦-in-point↑ pt[ x , 𝕤 ])
             goal (i , q) = lemma₁ x 𝕤 (B𝓓 [ i ]) (pr₂ (βₖ i)) (⊑ᴮₛ-to-⊑ᴮ q)

      ‡ : ((⋁ 𝒦-in-point↑ pt[ (x , 𝕤) ]) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (↓ᴮₛ-is-directed x))
      ‡ = sup-is-lowerbound-of-upperbounds
           (underlying-order 𝓓)
           (⋁-is-sup (𝒦-in-point↑ pt[ (x , 𝕤) ]))
           (∐ 𝓓 (↓ᴮₛ-is-directed x))
           goal
            where
             goal : is-upperbound
                     (underlying-order 𝓓)
                     (∐ 𝓓 (↓ᴮₛ-is-directed x))
                     (𝒦-in-point pt[ x , 𝕤 ] [_])
             goal (i , q) = ∐-is-upperbound 𝓓 (↓ᴮₛ-is-directed x) (i , ⊑ᴮ-to-⊑ᴮₛ q)

 sharp-cancels-pt : (𝓍 : ♯𝓓) → sharp 𝓅𝓉[ 𝓍 ] ＝ 𝓍
 sharp-cancels-pt 𝓍@(x , 𝕤) = to-sharp-＝ (sharp 𝓅𝓉[ 𝓍 ]) 𝓍 †
  where
   † : ⦅ sharp 𝓅𝓉[ 𝓍 ] ⦆ ＝ x
   † = ⦅ sharp 𝓅𝓉[ 𝓍 ] ⦆        ＝⟨ Ⅰ ⟩
       ∐ 𝓓 (↓ᴮₛ-is-directed x)  ＝⟨ Ⅱ ⟩
       ⦅ 𝓍 ⦆                    ∎
        where
         Ⅰ = lemma₄ x 𝕤 ⁻¹
         Ⅱ = ↓ᴮₛ-∐-＝ ⦅ 𝓍 ⦆

 open PropertiesAlgebraic 𝓓 𝕒

 another-lemma : (𝔘 : ⟨ 𝒪 σ⦅𝓓⦆ ⟩) (ℱ@(F , _) : Point σ⦅𝓓⦆)
               → (sharp₀ ℱ ∈ₛ 𝔘 ⇒ F 𝔘) holds
 another-lemma 𝔘 ℱ@(F , 𝒽) = †
  where
   open 𝒪ₛᴿ (to-𝒪ₛᴿ 𝔘)

   † : (sharp₀ ℱ ∈ₛ 𝔘 ⇒ F 𝔘) holds
   † p = ∥∥-rec (holds-is-prop (F 𝔘)) †₁ (pred-is-inaccessible-by-dir-joins (𝒦-in-point↑ ℱ) p)
    where
     †₁ : Σ i ꞉ index (pr₁ (𝒦-in-point↑ ℱ)) , pred (pr₁ (𝒦-in-point↑ ℱ) [ i ]) holds
       → F 𝔘 holds
     †₁ ((a , b) , c) = frame-morphisms-are-monotonic F 𝒽 (↑ˢ[ βₖ a ] , 𝔘) foo b
      where
       foo : (↑ˢ[ βₖ a ] ≤[ poset-of (𝒪 σ⦅𝓓⦆) ] 𝔘) holds
       foo x = pred-is-upwards-closed (B𝓓 [ a ]) (B𝓓 [ x ]) c

 final-lemma : (ks : List (index B𝓓)) (ℱ@(F , _) : Point σ⦅𝓓⦆)
             → (F (𝜸 ks) ⇒ sharp₀ ℱ ∈ₛ 𝜸 ks) holds
 final-lemma []       ℱ@(F , _) p = 𝟘-elim quux
  where
   φ : F 𝟎[ 𝒪 σ⦅𝓓⦆ ] holds
   φ = transport (λ - → (F -) holds) (𝜸-equal-to-𝜸₁ []) p

   baz : 𝟎[ 𝟎-𝔽𝕣𝕞 pe ] holds
   baz = transport _holds (frame-homomorphisms-preserve-bottom ℱ) φ

   quux : ⊥ₚ holds
   quux = transport (λ - → - holds) (𝟎-is-⊥ pe ⁻¹) baz

 final-lemma (k ∷ ks) ℱ@(F , _) p =
  ∥∥-rec (holds-is-prop ((sharp₀ ℱ ∈ₛ 𝜸 (k ∷ ks)))) ‡ †
   where
    foo : F (𝜸 (k ∷ ks)) ＝ F ↑ᵏ[ k ] ∨ F (𝜸 ks)
    foo = F (𝜸 (k ∷ ks))                     ＝⟨ ap F (𝜸-equal-to-𝜸₁ (k ∷ ks)) ⟩
          F (𝜸₁ (k ∷ ks))                    ＝⟨ frame-homomorphisms-preserve-binary-joins ℱ _ _  ⟩
          F ↑ᵏ[ k ] ∨[ 𝟎-𝔽𝕣𝕞 pe ] F (𝜸₁ ks)  ＝⟨ Ⅲ ⟩
          F ↑ᵏ[ k ] ∨[ 𝟎-𝔽𝕣𝕞 pe ] F (𝜸 ks)   ＝⟨ Ⅳ ⟩
          F ↑ᵏ[ k ] ∨ F (𝜸 ks)               ∎
           where
            Ⅲ = ap (λ - → F ↑ᵏ[ k ] ∨[ 𝟎-𝔽𝕣𝕞 pe ] F -) (𝜸-equal-to-𝜸₁ ks ⁻¹)
            Ⅳ = binary-join-is-disjunction pe (F ↑ᵏ[ k ]) (F (𝜸 ks))

    † : (F ↑ᵏ[ k ] ∨ F (𝜸 ks)) holds
    † = transport _holds foo p

    ‡ : F ↑ᵏ[ k ] holds + F (𝜸 ks) holds → (sharp₀ ℱ ∈ₛ 𝜸 (k ∷ ks)) holds
    ‡ (inl p) = ∣ inl (∐-is-upperbound 𝓓 (𝒦-in-point-is-directed ℱ) (k , p)) ∣
    ‡ (inr q) = ∣ inr (final-lemma ks ℱ q) ∣

 pt-cancels-sharp : (ℱ : Spectral-Point σ⦅𝓓⦆) → 𝓅𝓉[ sharp ℱ ] ＝ ℱ
 pt-cancels-sharp ℱ =
  to-spectral-point-＝ σ⦅𝓓⦆ 𝓅𝓉[ sharp ℱ ] ℱ (dfunext fe †)
   where
    open Spectral-Point σ⦅𝓓⦆ ℱ renaming (point-fn to F; point to ℱ₀)

    † : (𝔘 : ⟨ 𝒪 σ⦅𝓓⦆ ⟩) → (sharp₀ ℱ₀ ∈ₛ 𝔘) ＝ F 𝔘
    † 𝔘@(U , s) = transport (λ - → (sharp₀ ℱ₀ ∈ₛ -) ＝ F -) (q ⁻¹) nts
     where
      S : Fam 𝓤 ⟨ 𝒪 σ⦅𝓓⦆ ⟩
      S = covering-familyₛ σ⦅𝓓⦆ σᴰ 𝔘

      q : 𝔘 ＝ ⋁[ 𝒪 σ⦅𝓓⦆ ] S
      q = basisₛ-covers-do-cover-eq σ⦅𝓓⦆ σᴰ 𝔘

      nts₁ : cofinal-in (𝟎-𝔽𝕣𝕞 pe) ⁅ sharp₀ ℱ₀ ∈ₛ 𝔘 ∣ 𝔘 ε S ⁆ ⁅ F 𝔘 ∣ 𝔘 ε S ⁆ holds
      nts₁ k = ∣ k , another-lemma (S [ k ]) ℱ₀ ∣

      nts₂ : cofinal-in (𝟎-𝔽𝕣𝕞 pe) ⁅ F 𝔘 ∣ 𝔘 ε S ⁆ ⁅ sharp₀ ℱ₀ ∈ₛ 𝔘 ∣ 𝔘 ε S ⁆ holds
      nts₂ (ks , p) = ∣ (ks , p) , final-lemma ks ℱ₀ ∣

      nts : sharp₀ ℱ₀ ∈ₛ (⋁[ 𝒪 σ⦅𝓓⦆ ] S) ＝ F (⋁[ 𝒪 σ⦅𝓓⦆ ] S)
      nts = sharp₀ ℱ₀ ∈ₛ (⋁[ 𝒪 σ⦅𝓓⦆ ] S)                  ＝⟨ refl ⟩
            pt₀[ sharp₀ ℱ₀ ] (⋁[ 𝒪 σ⦅𝓓⦆ ] S)              ＝⟨ Ⅰ ⟩
            ⋁[ 𝟎-𝔽𝕣𝕞 pe ] ⁅ pt₀[ sharp₀ ℱ₀ ] 𝔘 ∣ 𝔘  ε S ⁆  ＝⟨ refl ⟩
            ⋁[ 𝟎-𝔽𝕣𝕞 pe ] ⁅ sharp₀ ℱ₀ ∈ₛ 𝔘 ∣ 𝔘 ε S ⁆       ＝⟨ bicofinal-implies-same-join (𝟎-𝔽𝕣𝕞 pe) ⁅ sharp₀ ℱ₀ ∈ₛ 𝔘 ∣ 𝔘 ε S ⁆ ⁅ F 𝔘 ∣ 𝔘 ε S ⁆ nts₁ nts₂ ⟩
            ⋁[ 𝟎-𝔽𝕣𝕞 pe ] ⁅ F 𝔘 ∣ 𝔘 ε S ⁆                  ＝⟨ Ⅴ ⟩
            F (⋁[ 𝒪 σ⦅𝓓⦆ ] S)                              ∎
             where
              Ⅰ = frame-homomorphisms-preserve-all-joins′ (𝒪 σ⦅𝓓⦆) (𝟎-𝔽𝕣𝕞 pe) pt[ sharp ℱ ] S
              Ⅴ = frame-homomorphisms-preserve-all-joins′ (𝒪 σ⦅𝓓⦆) (𝟎-𝔽𝕣𝕞 pe) ℱ₀ S ⁻¹

 ♯𝓓-equivalent-to-spectral-points-of-σ⦅𝓓⦆ : ♯𝓓 ≃ Spectral-Point σ⦅𝓓⦆
 ♯𝓓-equivalent-to-spectral-points-of-σ⦅𝓓⦆ = 𝓅𝓉[_] , qinvs-are-equivs 𝓅𝓉[_] †
  where
   † : qinv 𝓅𝓉[_]
   † = sharp , sharp-cancels-pt , pt-cancels-sharp

\end{code}
