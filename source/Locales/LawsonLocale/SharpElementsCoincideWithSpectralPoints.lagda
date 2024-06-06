---
title:          Equivalence of sharp elements with spectral points
author:         Ayberk Tosun
date-started:   2024-05-22
date-completed: 2024-05-28
dates-updated:  [2024-06-03]
---

This module contains the proof of equivalence between the sharp elements of a
Scott domain and the “spectral points” of its Scott locale. This equivalence was
conjectured by Martín Escardó and proved by Ayberk Tosun on 2024-03-15.

The formalization of the proof was completed on 2024-05-28.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.List hiding ([_])
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
open Locale
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

is-decidableₚ : Ω 𝓤 → Ω 𝓤
is-decidableₚ P =
 is-decidable (P holds) , decidability-of-prop-is-prop fe (holds-is-prop P)

\end{code}

\section{Introduction}

We work in a module parameterized by

 - a large and locally small Scott domain `𝓓`,
 - assumed to satisfy the `decidability-condition` which says that upper
   boundedness of its compact elements is a decidable property.

\begin{code}

module Sharp-Element-Spectral-Point-Equivalence
        (𝓓    : DCPO {𝓤 ⁺} {𝓤})
        (hl   : has-least (underlying-order 𝓓))
        (sd   : is-scott-domain 𝓓 holds)
        (dc   : decidability-condition 𝓓)
       where

 open Construction 𝓓 ua hl sd dc
 open DefinitionOfBoundedCompleteness hiding (_⊑_)

\end{code}

The following is a bit of preparation for the proofs. We open up relevant
modules and define abbreviations for constructions that we use for the sake of
readability and self-containment.

\begin{code}

 𝒷₀ : has-unspecified-small-compact-basis 𝓓
 𝒷₀ = pr₁ sd

\end{code}

We denote by `Scott⦅𝓓⦆` the Scott locale of domain `𝓓`.

\begin{code}

 open SpectralScottLocaleConstruction₂ 𝓓 ua hl sd dc pe renaming (σ⦅𝓓⦆ to Scott⦅𝓓⦆)

\end{code}

For the frame of opens of the Scott locale `Scott⦅𝓓⦆`, we reserve the notation
`σ⦅𝓓⦆`. This notation differs from other uses in TypeTopology, but it should be
the standard one and the notation elsewhere should be updated to use this one.

\begin{code}

 σ⦅𝓓⦆ : Frame (𝓤 ⁺) 𝓤 𝓤
 σ⦅𝓓⦆ = 𝒪 Scott⦅𝓓⦆

 open SpectralScottLocaleConstruction  𝓓 hl hscb dc bc pe hiding (scb; σᴰ)

 open ScottLocaleProperties 𝓓 hl hscb pe renaming (⊤-is-compact to Scott⦅𝓓⦆-is-compact)
 open is-small-compact-basis scb
 open structurally-algebraic

 σᴰ : spectralᴰ Scott⦅𝓓⦆
 σᴰ = scott-locale-spectralᴰ

\end{code}

The family `basis` given below is the basis of the Scott locale of domain `𝓓`.

\begin{code}

 basis : Fam 𝓤 ⟨ 𝒪 Scott⦅𝓓⦆ ⟩
 basis = basisₛ Scott⦅𝓓⦆ σᴰ

 Bσ : 𝓤  ̇
 Bσ = index basis

 βσ : Bσ → ⟨ 𝒪 Scott⦅𝓓⦆ ⟩
 βσ = basis [_]

 κσ : (i : Bσ) → is-compact-open Scott⦅𝓓⦆ (βσ i) holds
 κσ = basisₛ-consists-of-compact-opens Scott⦅𝓓⦆ σᴰ

\end{code}

We define a version of the order of `𝓓` that is packaged up with the proof that
it is a proposition (called `prop-valuedness` in the domain theory development).

\begin{code}

 _⊑_ : ⟨ 𝓓 ⟩∙ → ⟨ 𝓓 ⟩∙ → Ω 𝓤
 x ⊑ y = (x ⊑⟨ 𝓓 ⟩ y) , prop-valuedness 𝓓 x y

\end{code}

\section{Definition of sharpness}

We now define what it means for an element to be _sharp_, following the work of
de Jong [1].

\begin{code}

 is-sharp : ⟨ 𝓓 ⟩∙ → Ω (𝓤 ⁺)
 is-sharp x = Ɐ c ꞉ ⟨ 𝓓 ⟩∙ , is-compactₚ 𝓓 c ⇒ is-decidableₚ (c ⊑ x)

\end{code}

This definition of the notion of sharpness is a predicate with large truth
values as it quantifies over the compact opens. Because we are working with an
algebraic dcpo, however, we can define a small version which we denote
`is-sharp⁻`.

\begin{code}

 is-sharp⁻ : ⟨ 𝓓 ⟩∙ → Ω 𝓤
 is-sharp⁻ x = Ɐ i ꞉ index B𝓓 , is-decidableₚ ((B𝓓 [ i ]) ⊑ x)

\end{code}

These two are equivalent.

\begin{code}

 sharp-implies-sharp⁻ : (Ɐ x ꞉ ⟨ 𝓓 ⟩∙ , is-sharp x ⇒ is-sharp⁻ x) holds
 sharp-implies-sharp⁻ x 𝕤 i = 𝕤 (B𝓓 [ i ]) (basis-is-compact i)

 sharp⁻-implies-sharp : (Ɐ x ꞉ ⟨ 𝓓 ⟩∙ , is-sharp⁻ x ⇒ is-sharp x) holds
 sharp⁻-implies-sharp x 𝕤 c χ =
  ∥∥-rec (holds-is-prop (is-decidableₚ (c ⊑ x))) † μ
   where
    μ : ∃ i ꞉ index B𝓓 , B𝓓 [ i ] ＝ c
    μ = small-compact-basis-contains-all-compact-elements 𝓓 (B𝓓 [_]) scb c χ

    † : Σ i ꞉ index B𝓓 , B𝓓 [ i ] ＝ c → is-decidableₚ (c ⊑ x) holds
    † (i , p) = transport (λ - → is-decidableₚ (- ⊑ x) holds) p (𝕤 i)

 sharp-is-equivalent-to-sharp⁻ : (Ɐ x ꞉ ⟨ 𝓓 ⟩∙ , is-sharp x ⇔ is-sharp⁻ x) holds
 sharp-is-equivalent-to-sharp⁻ x =
  sharp-implies-sharp⁻ x , sharp⁻-implies-sharp x

\end{code}

We now define the type `♯𝓓` of sharp elements of the Scott domain `𝓓`.

\begin{code}

 ♯𝓓 : 𝓤 ⁺  ̇
 ♯𝓓 = Σ x ꞉ ⟨ 𝓓 ⟩∙ , is-sharp x holds

\end{code}

We usually pattern match on the inhabitants of `♯𝓓` to refer to the first
component. But if the need arises, we denote the underlying element of a sharp
element `𝓍` by `⦅ 𝓍 ⦆`.

\begin{code}

 ⦅_⦆ : ♯𝓓 → ⟨ 𝓓 ⟩∙
 ⦅_⦆ (x , _) = x

 abstract
  to-sharp-＝ : (𝓍 𝓎 : ♯𝓓) → pr₁ 𝓍 ＝ pr₁ 𝓎 → 𝓍 ＝ 𝓎
  to-sharp-＝ 𝓍 𝓎 = to-subtype-＝ (holds-is-prop ∘ is-sharp)

 open Preliminaries
 open Locale
 open DefnOfScottTopology 𝓓 𝓤

\end{code}

\section{Characterization of sharp elements}

In this section, we give a characterization of sharp elements which we use
when constructing the equivalence (in the next section).

We define the following predicate expressing that an element `x` has decidable
membership in compact Scott opens.

\begin{code}

 open Properties 𝓓

 admits-decidable-membership-in-compact-scott-opens : ⟨ 𝓓 ⟩∙ → Ω (𝓤 ⁺)
 admits-decidable-membership-in-compact-scott-opens x =
  Ɐ 𝒦 ꞉ ⟨ 𝒪 Scott⦅𝓓⦆ ⟩ , is-compact-open Scott⦅𝓓⦆ 𝒦 ⇒ is-decidableₚ (x ∈ₛ 𝒦)

\end{code}

Every sharp element admits decidable membership in compact Scott opens.

\begin{code}

 sharp-implies-admits-decidable-membership-in-compact-scott-opens
  : (x : ⟨ 𝓓 ⟩∙)
  → (is-sharp x ⇒ admits-decidable-membership-in-compact-scott-opens x) holds
 sharp-implies-admits-decidable-membership-in-compact-scott-opens x 𝓈𝒽 𝒦 𝕜 =
  ∥∥-rec (holds-is-prop (is-decidableₚ (x ∈ₛ 𝒦))) (uncurry ‡) ♢
   where
    ♢ : is-basic Scott⦅𝓓⦆ 𝒦 (spectralᴰ-implies-directed-basisᴰ Scott⦅𝓓⦆ σᴰ) holds
    ♢ = compact-opens-are-basic
         Scott⦅𝓓⦆
         (spectralᴰ-implies-directed-basisᴰ Scott⦅𝓓⦆ σᴰ)
         𝒦
         𝕜

    lemma : (xs : List (index B𝓓)) → is-decidableₚ (x ∈ₛ βσ xs) holds
    lemma []       = inr 𝟘-elim
    lemma (i ∷ is) =
     ∨-preserves-decidability pt (x ∈ₛ ↑ˢ[ βₖ i ]) (x ∈ₛ 𝜸 is) † IH
      where
       † : is-decidableₚ (x ∈ₛ ↑ˢ[ βₖ i ]) holds
       † = 𝓈𝒽 (β i) (basis-is-compact i)

       IH : is-decidableₚ (x ∈ₛ 𝜸 is) holds
       IH = lemma is

    ‡ : (xs : List (index B𝓓)) → βσ xs ＝ 𝒦 → is-decidableₚ (x ∈ₛ 𝒦) holds
    ‡ xs p = transport (λ - → is-decidableₚ (x ∈ₛ -) holds) p (lemma xs)

\end{code}

The converse also holds meaning elements that admit decidable membership in
compact Scott opens are _exactly_ the sharp elements.

\begin{code}

 admits-decidable-membership-in-compact-scott-opens-implies-is-sharp
  : (x : ⟨ 𝓓 ⟩∙)
  → admits-decidable-membership-in-compact-scott-opens x holds
  → is-sharp x holds
 admits-decidable-membership-in-compact-scott-opens-implies-is-sharp x φ c 𝕜 =
  φ ↑ˢ[ (c , 𝕜) ] (principal-filter-is-compact₀ c 𝕜)

 characterization-of-sharp-elements
  : (x : ⟨ 𝓓 ⟩∙)
  → (admits-decidable-membership-in-compact-scott-opens x ⇔ is-sharp x) holds
 characterization-of-sharp-elements x = † , ‡
  where
   † = admits-decidable-membership-in-compact-scott-opens-implies-is-sharp x
   ‡ = sharp-implies-admits-decidable-membership-in-compact-scott-opens x

\end{code}

\section{The equivalence}

We now start constructing an equivalence between the type
`Spectral-Point Scott⦅𝓓⦆` and the type `♯𝓓`.

This equivalence consists of the maps:

  1. `𝓅𝓉[_] : ♯𝓓 → Spectral-Point Scott⦅𝓓⦆`, and
  2. `sharp : Spectral-Point Scott⦅𝓓⦆ → ♯𝓓`.

We now construct these maps in this order.

\subsection{Definition of the map `𝓅𝓉`}

We follow our usual convention of distinguishing the preliminary version of the
construction of interest using the subscript `₀`, which we then package up with
the proof that it satisfies some property.

\begin{code}

 pt₀[_] : ⟨ 𝓓 ⟩∙ → ⟨ 𝒪 Scott⦅𝓓⦆ ⟩ → Ω 𝓤
 pt₀[_] x U = x ∈ₛ U

 open FrameHomomorphismProperties (𝒪 Scott⦅𝓓⦆) (𝟎-𝔽𝕣𝕞 pe)
 open FrameHomomorphisms

 pt[_] : ♯𝓓 → Point Scott⦅𝓓⦆
 pt[_] 𝓍@(x , 𝕤) = pt₀[ x ] , †
  where
   ‡ : preserves-joins (𝒪 Scott⦅𝓓⦆) (𝟎-𝔽𝕣𝕞 pe) pt₀[ x ] holds
   ‡ S = ⋁[ 𝟎-𝔽𝕣𝕞 pe ]-upper ⁅ pt₀[ x ] y ∣ y ε S ⁆
       , ⋁[ 𝟎-𝔽𝕣𝕞 pe ]-least ⁅ pt₀[ x ] y ∣ y ε S ⁆

   † : is-a-frame-homomorphism (𝒪 Scott⦅𝓓⦆) (𝟎-𝔽𝕣𝕞 pe) pt₀[ x ] holds
   † = refl , (λ _ _ → refl) , ‡

 open BottomLemma 𝓓 𝕒 hl

\end{code}

Given any sharp element `𝓍`, the point `pt 𝓍` is a spectral map.

\begin{code}

 pt-is-spectral : (𝓍 : ♯𝓓) → is-spectral-map Scott⦅𝓓⦆ (𝟏Loc pe) pt[ 𝓍 ] holds
 pt-is-spectral 𝓍@(x , 𝓈𝒽) 𝒦@(K , σ) 𝕜 = decidable-implies-compact pe (x ∈ₛ 𝒦) †
  where
   † : is-decidableₚ (x ∈ₛ (K , σ)) holds
   † = sharp-implies-admits-decidable-membership-in-compact-scott-opens x 𝓈𝒽 𝒦 𝕜

 open Notion-Of-Spectral-Point pe

\end{code}

We package `pt[_]` up with this proof of spectrality and denote it `𝓅𝓉[_]`.

\begin{code}

 𝓅𝓉[_] : ♯𝓓 → Spectral-Point Scott⦅𝓓⦆
 𝓅𝓉[_] 𝓍 = to-spectral-point Scott⦅𝓓⦆ ℱ
  where
   ℱ : Spectral-Map (𝟏Loc pe) Scott⦅𝓓⦆
   ℱ = pt[ 𝓍 ] , pt-is-spectral 𝓍

\end{code}

\subsection{Definition of the map `sharp`}

We now define the map `sharp` going in the opposite direction.

\begin{code}

 sharp₀ : Point Scott⦅𝓓⦆ → ⟨ 𝓓 ⟩∙
 sharp₀ ℱ = ∐ 𝓓 (𝒦-in-point-is-directed ℱ)

\end{code}

The following lemma says if `sharp(ℱ) ∈ 𝔘` then `U ∈ ℱ`, for every point `ℱ` and
every Scott open `𝔘`.

\begin{code}

 open PropertiesAlgebraic 𝓓 𝕒 hiding (is-compactₚ)

 sharp-in-scott-open-implies-in-point
  : (𝔘 : ⟨ 𝒪 Scott⦅𝓓⦆ ⟩)
  → (ℱ@(F , _) : Point Scott⦅𝓓⦆)
  → (sharp₀ ℱ ∈ₛ 𝔘 ⇒ F 𝔘) holds
 sharp-in-scott-open-implies-in-point 𝔘 ℱ@(F , 𝒽) = †
  where
   open 𝒪ₛᴿ (to-𝒪ₛᴿ 𝔘)

   † : (sharp₀ ℱ ∈ₛ 𝔘 ⇒ F 𝔘) holds
   † p = ∥∥-rec (holds-is-prop (F 𝔘)) ‡ γ
    where
     ‡ : Σ (i , _) ꞉ index (𝒦-in-point ℱ) , ((B𝓓 [ i ]) ∈ₛ 𝔘) holds
       → F 𝔘 holds
     ‡ ((a , b) , c) = frame-morphisms-are-monotonic F 𝒽 (↑ˢ[ βₖ a ] , 𝔘) q b
      where
       q : (↑ˢ[ βₖ a ] ≤[ poset-of (𝒪 Scott⦅𝓓⦆) ] 𝔘) holds
       q x = pred-is-upwards-closed (B𝓓 [ a ]) (B𝓓 [ x ]) c

     γ : ∥ Σ (i , _) ꞉ index (𝒦-in-point ℱ) , ((B𝓓 [ i ]) ∈ₛ 𝔘) holds ∥
     γ = pred-is-inaccessible-by-dir-joins (𝒦-in-point↑ ℱ) p

\end{code}

As an immediate special case of this lemma, we obtain the following.

\begin{code}

 below-sharp-implies-in-point
  : (ℱ@(F , _) : Point Scott⦅𝓓⦆)
  → (c : ⟨ 𝓓 ⟩∙)
  → (𝕜 : is-compact 𝓓 c)
  → c ⊑⟨ 𝓓 ⟩ sharp₀ ℱ
  → F ↑ˢ[ c , 𝕜 ] holds
 below-sharp-implies-in-point ℱ@(F , 𝒽) c 𝕜 =
  sharp-in-scott-open-implies-in-point ↑ˢ[ 𝔠 ] ℱ
   where
    𝔠 = (c , 𝕜)

\end{code}

The converse of this special case also holds. In fact, the converse holds
for _all_ compact Scott opens.

\begin{code}

 in-point-implies-contains-sharp⋆
  : (ks : List (index B𝓓))
  → (ℱ@(F , _) : Point Scott⦅𝓓⦆)
  → (F (𝜸 ks) ⇒ sharp₀ ℱ ∈ₛ 𝜸 ks) holds
 in-point-implies-contains-sharp⋆ [] ℱ@(F , _) p = 𝟘-elim Ⅰ
  where
   φ : F 𝟎[ 𝒪 Scott⦅𝓓⦆ ] holds
   φ = transport (λ - → (F -) holds) (𝜸-equal-to-𝜸₁ []) p

   Ⅱ : 𝟎[ 𝟎-𝔽𝕣𝕞 pe ] holds
   Ⅱ = transport _holds (frame-homomorphisms-preserve-bottom ℱ) φ

   Ⅰ : ⊥ₚ holds
   Ⅰ = transport (λ - → - holds) (𝟎-is-⊥ pe ⁻¹) Ⅱ

 in-point-implies-contains-sharp⋆ (k ∷ ks) ℱ@(F , _) p =
  ∥∥-rec (holds-is-prop ((sharp₀ ℱ ∈ₛ 𝜸 (k ∷ ks)))) ‡ (transport _holds ♠ p)
   where
    ♠ : F (𝜸 (k ∷ ks)) ＝ F ↑ᵏ[ k ] ∨ F (𝜸 ks)
    ♠ = F (𝜸 (k ∷ ks))                     ＝⟨ Ⅰ ⟩
        F (𝜸₁ (k ∷ ks))                    ＝⟨ Ⅱ ⟩
        F ↑ᵏ[ k ] ∨[ 𝟎-𝔽𝕣𝕞 pe ] F (𝜸₁ ks)  ＝⟨ Ⅲ ⟩
        F ↑ᵏ[ k ] ∨[ 𝟎-𝔽𝕣𝕞 pe ] F (𝜸 ks)   ＝⟨ Ⅳ ⟩
        F ↑ᵏ[ k ] ∨ F (𝜸 ks)               ∎
         where
          Ⅰ = ap F (𝜸-equal-to-𝜸₁ (k ∷ ks))
          Ⅱ = frame-homomorphisms-preserve-binary-joins ℱ _ _
          Ⅲ = ap (λ - → F ↑ᵏ[ k ] ∨[ 𝟎-𝔽𝕣𝕞 pe ] F -) (𝜸-equal-to-𝜸₁ ks ⁻¹)
          Ⅳ = binary-join-is-disjunction pe (F ↑ᵏ[ k ]) (F (𝜸 ks))

    ‡ : F ↑ᵏ[ k ] holds + F (𝜸 ks) holds → (sharp₀ ℱ ∈ₛ 𝜸 (k ∷ ks)) holds
    ‡ (inl p) = ∣ inl (∐-is-upperbound 𝓓 (𝒦-in-point-is-directed ℱ) (k , p)) ∣
    ‡ (inr q) = ∣ inr (in-point-implies-contains-sharp⋆ ks ℱ q) ∣

\end{code}

We can reformulate this more concisely to say the same thing for any compact
Scott open `K` since a Scott open is compact iff it is a finite join of
principal filters on compact opens.

\begin{code}

 in-point-implies-contains-sharp
  : (ℱ@(F , _) : Point Scott⦅𝓓⦆)
  → (K : ⟨ σ⦅𝓓⦆ ⟩)
  → (𝕜 : is-compact-open Scott⦅𝓓⦆ K holds)
  → (F K ⇒ sharp₀ ℱ ∈ₛ K) holds
 in-point-implies-contains-sharp ℱ@(F , ψ) K 𝕜 χ =
  ∥∥-rec (holds-is-prop (sharp₀ ℱ ∈ₛ K)) † γ
   where
    ℬ↑ : directed-basisᴰ (𝒪 Scott⦅𝓓⦆)
    ℬ↑ = spectralᴰ-implies-directed-basisᴰ Scott⦅𝓓⦆ σᴰ

    γ : is-basic Scott⦅𝓓⦆ K (spectralᴰ-implies-directed-basisᴰ Scott⦅𝓓⦆ σᴰ) holds
    γ = compact-opens-are-basic Scott⦅𝓓⦆ ℬ↑ K 𝕜

    † : Σ i ꞉ Bσ , βσ i ＝ K → (sharp₀ ℱ ∈ₛ K) holds
    † (i , p) = transport (λ - → (sharp₀ ℱ ∈ₛ -) holds) p ‡
     where
      μ : F (𝜸 i) holds
      μ = transport (λ - → F - holds) (p ⁻¹) χ

      ‡ : (sharp₀ (F , ψ) ∈ₛ βσ i) holds
      ‡ = in-point-implies-contains-sharp⋆ i ℱ μ

\end{code}

We now prove that the map `sharp₀` always gives sharp elements.

\begin{code}

 sharp₀-gives-sharp-elements : (F : Point Scott⦅𝓓⦆)
                             → is-spectral-map Scott⦅𝓓⦆ (𝟏Loc pe) F holds
                             → is-sharp (sharp₀ F) holds
 sharp₀-gives-sharp-elements ℱ@(F , _) σ c 𝕜 = cases case₁ case₂ γ
  where
   χ : is-compact-open (𝟏Loc pe) (F ↑ˢ[ c , 𝕜 ]) holds
   χ = σ ↑ˢ[ c , 𝕜 ] (principal-filter-is-compact₀ c 𝕜 )

   γ : is-decidableₚ (F ↑ˢ[ c , 𝕜 ]) holds
   γ = compact-implies-boolean pe (F ↑ˢ[ c , 𝕜 ]) χ

   κ : is-compact-open Scott⦅𝓓⦆ ↑ˢ[ c , 𝕜 ] holds
   κ = principal-filter-is-compact₀ c 𝕜

   case₁ : F ↑ˢ[ c , 𝕜 ] holds → is-decidableₚ (c ⊑ sharp₀ ℱ) holds
   case₁ = inl ∘ in-point-implies-contains-sharp ℱ ↑ˢ[ (c , 𝕜) ] κ

   case₂ : ¬ (F ↑ˢ[ c , 𝕜 ] holds) → is-decidableₚ (c ⊑ sharp₀ ℱ) holds
   case₂ χ = inr (χ ∘ below-sharp-implies-in-point ℱ c 𝕜)

\end{code}

We denote by `sharp` the version of `sharp₀` that is packaged up with the proof
that it always gives sharp elements.

\begin{code}

 sharp : Spectral-Point Scott⦅𝓓⦆ → ♯𝓓
 sharp ℱ = sharp₀ F· , sharp₀-gives-sharp-elements F· σ
  where
   open Spectral-Point Scott⦅𝓓⦆ ℱ
    renaming (point-fn to F; point to F·; point-preserves-compactness to σ)

\end{code}

\subsection{A useful lemma}

We now prove a lemma which we use when showing that these two maps form an
equivalence.

Given a sharp element `𝓍`, the element `sharp (pt 𝓍)` is exactly the join of
the compact approximants of `𝓍`.

\begin{code}

 sharp-equal-to-join-of-covering-family
  : (𝓍 : ♯𝓓)
  → ∐ 𝓓 (↓ᴮₛ-is-directed ⦅ 𝓍 ⦆) ＝ sharp₀ pt[ 𝓍 ]
 sharp-equal-to-join-of-covering-family (x , 𝕤) =
  antisymmetry 𝓓 (∐ 𝓓 (↓ᴮₛ-is-directed x)) (⋁ 𝒦-in-point↑ pt[ (x , 𝕤) ]) † ‡
   where
    γ : ((i , _) : ↓ᴮₛ x) → (sharp₀ pt[ x , 𝕤 ] ∈ₛ ↑ˢ[ βₖ i ]) holds
    γ (i , q) = in-point-implies-contains-sharp
                 pt[ x , 𝕤 ]
                 ↑ˢ[ βₖ i ]
                 (principal-filter-is-compact i)
                 (⊑ᴮₛ-to-⊑ᴮ q)

    δ : is-upperbound
         (underlying-order 𝓓)
         (∐ 𝓓 (↓ᴮₛ-is-directed x))
         (𝒦-in-point pt[ x , 𝕤 ] [_])
    δ (i , q) = ∐-is-upperbound 𝓓 (↓ᴮₛ-is-directed x) (i , ⊑ᴮ-to-⊑ᴮₛ q)

    † : (∐ 𝓓 (↓ᴮₛ-is-directed x)) ⊑⟨ 𝓓 ⟩ (⋁ 𝒦-in-point↑ pt[ (x , 𝕤) ])
    † = ∐-is-lowerbound-of-upperbounds
         𝓓
         (↓ᴮₛ-is-directed x)
         (⋁ 𝒦-in-point↑ pt[ x , 𝕤 ])
         γ

    ‡ : ((⋁ 𝒦-in-point↑ pt[ (x , 𝕤) ]) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (↓ᴮₛ-is-directed x))
    ‡ = sup-is-lowerbound-of-upperbounds
         (underlying-order 𝓓)
         (⋁-is-sup (𝒦-in-point↑ pt[ (x , 𝕤) ]))
         (∐ 𝓓 (↓ᴮₛ-is-directed x))
         δ

\end{code}

\subsection{The equivalence proof}

The fact that `sharp` is a retraction of `𝓅𝓉[_]` follows easily from the lemma
`sharp-equal-to-join-of-covering-family` above.

\begin{code}

 sharp-cancels-pt : (𝓍 : ♯𝓓) → sharp 𝓅𝓉[ 𝓍 ] ＝ 𝓍
 sharp-cancels-pt 𝓍 = to-sharp-＝ (sharp 𝓅𝓉[ 𝓍 ]) 𝓍 †
  where
   † : ⦅ sharp 𝓅𝓉[ 𝓍 ] ⦆ ＝ ⦅ 𝓍 ⦆
   † = ⦅ sharp 𝓅𝓉[ 𝓍 ] ⦆           ＝⟨ Ⅰ ⟩
       ∐ 𝓓 (↓ᴮₛ-is-directed ⦅ 𝓍 ⦆) ＝⟨ Ⅱ ⟩
       ⦅ 𝓍 ⦆                       ∎
        where
         Ⅰ = sharp-equal-to-join-of-covering-family 𝓍 ⁻¹
         Ⅱ = ↓ᴮₛ-∐-＝ ⦅ 𝓍 ⦆

\end{code}

The map `𝓅𝓉[_]` is a retraction of the map `sharp`.

\begin{code}

 pt-cancels-sharp : (ℱ : Spectral-Point Scott⦅𝓓⦆) → 𝓅𝓉[ sharp ℱ ] ＝ ℱ
 pt-cancels-sharp ℱ =
  to-spectral-point-＝ Scott⦅𝓓⦆ 𝓅𝓉[ sharp ℱ ] ℱ (dfunext fe †)
   where
    open Spectral-Point Scott⦅𝓓⦆ ℱ renaming (point-fn to F; point to ℱ₀)

    † : (𝔘 : ⟨ 𝒪 Scott⦅𝓓⦆ ⟩) → (sharp₀ ℱ₀ ∈ₛ 𝔘) ＝ F 𝔘
    † 𝔘@(U , s) = transport (λ - → (sharp₀ ℱ₀ ∈ₛ -) ＝ F -) (q ⁻¹) ‡
     where
      S : Fam 𝓤 ⟨ 𝒪 Scott⦅𝓓⦆ ⟩
      S = covering-familyₛ Scott⦅𝓓⦆ σᴰ 𝔘

      q : 𝔘 ＝ ⋁[ 𝒪 Scott⦅𝓓⦆ ] S
      q = basisₛ-covers-do-cover-eq Scott⦅𝓓⦆ σᴰ 𝔘

      ‡₁ : cofinal-in (𝟎-𝔽𝕣𝕞 pe) ⁅ sharp₀ ℱ₀ ∈ₛ 𝔘 ∣ 𝔘 ε S ⁆ ⁅ F 𝔘 ∣ 𝔘 ε S ⁆ holds
      ‡₁ k = ∣ k , sharp-in-scott-open-implies-in-point (S [ k ]) ℱ₀ ∣

      ‡₂ : cofinal-in (𝟎-𝔽𝕣𝕞 pe) ⁅ F 𝔘 ∣ 𝔘 ε S ⁆ ⁅ sharp₀ ℱ₀ ∈ₛ 𝔘 ∣ 𝔘 ε S ⁆ holds
      ‡₂ (ks , p) = ∣ (ks , p) , in-point-implies-contains-sharp⋆ ks ℱ₀ ∣

      ‡ : sharp₀ ℱ₀ ∈ₛ (⋁[ 𝒪 Scott⦅𝓓⦆ ] S) ＝ F (⋁[ 𝒪 Scott⦅𝓓⦆ ] S)
      ‡ = sharp₀ ℱ₀ ∈ₛ (⋁[ 𝒪 Scott⦅𝓓⦆ ] S)               ＝⟨ refl ⟩
          pt₀[ sharp₀ ℱ₀ ] (⋁[ 𝒪 Scott⦅𝓓⦆ ] S)           ＝⟨ Ⅰ    ⟩
          ⋁[ 𝟎-𝔽𝕣𝕞 pe ] ⁅ pt₀[ sharp₀ ℱ₀ ] 𝔘 ∣ 𝔘  ε S ⁆  ＝⟨ refl ⟩
          ⋁[ 𝟎-𝔽𝕣𝕞 pe ] ⁅ sharp₀ ℱ₀ ∈ₛ 𝔘 ∣ 𝔘 ε S ⁆       ＝⟨ Ⅱ    ⟩
          ⋁[ 𝟎-𝔽𝕣𝕞 pe ] ⁅ F 𝔘 ∣ 𝔘 ε S ⁆                  ＝⟨ Ⅲ    ⟩
          F (⋁[ 𝒪 Scott⦅𝓓⦆ ] S)                          ∎
           where
            Ⅰ = frame-homomorphisms-preserve-all-joins′
                 (𝒪 Scott⦅𝓓⦆)
                 (𝟎-𝔽𝕣𝕞 pe)
                 pt[ sharp ℱ ]
                 S
            Ⅱ = bicofinal-implies-same-join
                 (𝟎-𝔽𝕣𝕞 pe)
                 ⁅ sharp₀ ℱ₀ ∈ₛ 𝔘 ∣ 𝔘 ε S ⁆
                 ⁅ F 𝔘 ∣ 𝔘 ε S ⁆
                 ‡₁
                 ‡₂
            Ⅲ = frame-homomorphisms-preserve-all-joins′
                 (𝒪 Scott⦅𝓓⦆)
                 (𝟎-𝔽𝕣𝕞 pe)
                 ℱ₀
                 S ⁻¹

\end{code}

Finally, we conclude this development by giving the equivalence between the
sharp elements and the spectral points.

\begin{code}

 ♯𝓓-equivalent-to-spectral-points-of-Scott⦅𝓓⦆ : ♯𝓓 ≃ Spectral-Point Scott⦅𝓓⦆
 ♯𝓓-equivalent-to-spectral-points-of-Scott⦅𝓓⦆ = 𝓅𝓉[_] , qinvs-are-equivs 𝓅𝓉[_] †
  where
   † : qinv 𝓅𝓉[_]
   † = sharp , sharp-cancels-pt , pt-cancels-sharp

\end{code}

\section{Acknowledgements}

I am grateful to Tom de Jong for his comments on a write-up of the proof
formalized in this module.

\section{References}

- [1]: Tom de Jong. *Apartness, sharp elements, and the Scott topology of
  domains*.

  Mathematical Structures in Computer Science, vol. 33, no. 7,
  pp 573-604, August 2023. doi:10.1017/S0960129523000282

  https://doi.org/10.1017/S0960129523000282
