---
title:          The spectral Scott locale of a Scott domain
author:         Ayberk Tosun
date-started:   2023-10-25
date-completed: 2023-11-26
---

In this module, we prove that the Scott locale of any Scott domain is a spectral
locale (provided that the domain in consideration is large and locally small and
satisfies a certain decidability condition).

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import MLTT.List hiding ([_])
open import Slice.Family
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Powerset-MultiUniverse
open import UF.Size
open import UF.Classifiers
open import UF.Univalence
open import UF.Embeddings
open import UF.EquivalenceExamples
open import MLTT.Negation

module Locales.ScottLocale.ScottLocalesOfScottDomains
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
        (𝓤  : Universe) where

open import DomainTheory.Basics.Dcpo                         pt fe 𝓤
 renaming (⟨_⟩ to ⟨_⟩∙)
 hiding   (is-directed)
open import DomainTheory.Basics.Pointed                      pt fe 𝓤
 renaming (⊥ to ⊥d)
open import DomainTheory.Basics.WayBelow                     pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Bases            pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity       pt fe 𝓤
open import DomainTheory.BasesAndContinuity.CompactBasis     pt fe 𝓤
open import Locales.ScottLocale.Definition                   pt fe 𝓤
open import DomainTheory.Topology.ScottTopology              pt fe 𝓤
open import DomainTheory.Topology.ScottTopologyProperties    pt fe 𝓤
open import Locales.Frame                                    pt fe
 hiding (∅)
open import Locales.Compactness                              pt fe
 hiding (is-compact)

open import Locales.SmallBasis pt fe sr

open AllCombinators pt fe

open Locale

open PropositionalTruncation pt hiding (_∨_)

\end{code}

The module:

\begin{code}

open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤

\end{code}

contains a proof that the Scott locale of any algebraic dcpo is a spectral
locale.

In this module, we extend this proof by showing that the Scott locale is
spectral.

\section{Preliminaries}

The following function expresses a list being contained in a given subset.

\begin{code}

_⊆⊆_ : {𝓤 𝓥 : Universe} {X : 𝓤  ̇} → List X → 𝓟 {𝓥} {𝓤} X → 𝓤 ⊔ 𝓥  ̇
_⊆⊆_ {_} {_} {X} xs U = (x : X) → member x xs → x ∈ U

\end{code}

We define the following predicate that expresses what it means for two elements
of a DCPO `𝓓` to be “bounded above”.

\begin{code}

bounded-above : (𝓓 : DCPO {𝓤 ⁺} {𝓤}) → ⟨ 𝓓 ⟩∙ → ⟨ 𝓓 ⟩∙ → Ω (𝓤 ⁺)
bounded-above 𝓓 x y = ∥ upper-bound (binary-family 𝓤 x y) ∥Ω
 where
  open Joins (λ a b → a ⊑⟨ 𝓓 ⟩ₚ b)

infix 30 bounded-above

syntax bounded-above 𝓓 x y = x ↑[ 𝓓 ] y

\end{code}

For the proof of spectrality, we will also need the following assumption

\begin{code}

decidability-condition : (𝓓 : DCPO {𝓤 ⁺} {𝓤}) → 𝓤 ⁺  ̇
decidability-condition 𝓓 =
 (x y : ⟨ 𝓓 ⟩∙) → is-decidable (bounded-above 𝓓 x y holds)

\end{code}

\section{The proof}

As mentioned previously, we assume a couple of things.

  1. The dcpo `𝓓` in consideration is large and locally small.
  2. It is pointed.
  3. It has a specified small compact basis.
  4. It satisfies the aforementioned decidability condition.
  5. It is bounded complete (which means it is a Scott domain when combined
     with the algebraicity condition).

\begin{code}

open import DomainTheory.BasesAndContinuity.ScottDomain pt fe 𝓤
open DefinitionOfBoundedCompleteness

module SpectralScottLocaleConstruction
        (𝓓    : DCPO {𝓤 ⁺} {𝓤})
        (hl   : has-least (underlying-order 𝓓))
        (hscb : has-specified-small-compact-basis 𝓓)
        (dc   : decidability-condition 𝓓)
        (bc   : bounded-complete 𝓓 holds)
        (pe   : propext 𝓤) where

 open ScottLocaleConstruction 𝓓 hscb pe

\end{code}

We denote by `Σ𝓓` the large and locally small Scott locale of the dcpo `𝓓`.

\begin{code}

 open import Locales.ScottLocale.Properties pt fe 𝓤
 open ScottLocaleProperties 𝓓 hl hscb pe

 Σ[𝓓] : Locale (𝓤 ⁺) 𝓤 𝓤
 Σ[𝓓] = Σ⦅𝓓⦆

\end{code}

We denote by `(B, β)` the algebraic basis of the pointed dcpo 𝓓 in consideration.

\begin{code}

 B : 𝓤  ̇
 B = index-of-compact-basis 𝓓 hscb

 β : B → ⟨ 𝓓 ⟩∙
 β i = family-of-basic-opens 𝓓 hscb i

 open structurally-algebraic

 scb : is-small-compact-basis 𝓓 (family-of-basic-opens 𝓓 hscb)
 scb = small-compact-basis 𝓓 hscb

 open is-small-compact-basis scb


 ϟ : (b : B) → is-compact 𝓓 (β b)
 ϟ = basis-is-compact

\end{code}

We define some nice notation for the prop-valued equality of the dcpo `𝓓`.

\begin{code}

 _＝ₚ_ : ⟨ 𝓓 ⟩∙ → ⟨ 𝓓 ⟩∙ → Ω (𝓤 ⁺)
 x ＝ₚ y = (x ＝ y) , sethood 𝓓

\end{code}

We now proceed to construct the intensional basis for the Scott locale.

\begin{code}

 open DefnOfScottTopology 𝓓 𝓤
 open Properties 𝓓

 open binary-unions-of-subsets pt

\end{code}

The basis is the family `(List B , 𝜸₀)`, where `𝜸₀` is the following function:

\begin{code}

 𝜸₀ : List B → 𝓟 {𝓤} {𝓤 ⁺} ⟨ 𝓓 ⟩∙
 𝜸₀ = foldr _∪_ ∅ ∘ map (principal-filter 𝓓 ∘ β)

 𝜸₀-is-upwards-closed : (ks : List B)
                      → is-upwards-closed (𝜸₀ ks) holds
 𝜸₀-is-upwards-closed []       x y () q
 𝜸₀-is-upwards-closed (b ∷ bs) x y p  q =
  ∥∥-rec (holds-is-prop (y ∈ₚ 𝜸₀ (b ∷ bs))) † p
   where
    † : (β b ⊑⟨ 𝓓 ⟩ x) + x ∈ 𝜸₀ bs → 𝜸₀ (b ∷ bs) y holds
    † (inl r) = ∣ inl (principal-filter-is-upwards-closed (β b) x y r q) ∣
    † (inr r) = ∣ inr (𝜸₀-is-upwards-closed bs x y r q) ∣

 𝜸₀-is-inaccessible-by-directed-joins : (ks : List B)
                                             → is-inaccessible-by-directed-joins
                                                (𝜸₀ ks)
                                                 holds
 𝜸₀-is-inaccessible-by-directed-joins []       (S , δ) ()
 𝜸₀-is-inaccessible-by-directed-joins (k ∷ ks) (S , δ) p =
  ∥∥-rec ∃-is-prop † p
   where
    σ : is-scott-open (↑[ 𝓓 ] β k) holds
    σ = compact-implies-principal-filter-is-scott-open (β k) (basis-is-compact k)

    υ : is-upwards-closed (↑[ 𝓓 ] (β k)) holds
    υ = 𝒪ₛᴿ.pred-is-upwards-closed (to-𝒪ₛᴿ (↑[ 𝓓 ] (β k) , σ))

    ι : is-inaccessible-by-directed-joins (↑[ 𝓓 ] β k) holds
    ι = 𝒪ₛᴿ.pred-is-inaccessible-by-dir-joins (to-𝒪ₛᴿ (↑[ 𝓓 ] (β k) , σ))

    † : (β k ⊑⟨ 𝓓 ⟩ (⋁ (S , δ))) + (⋁ (S , δ)) ∈ 𝜸₀ ks
      → ∃ i ꞉ index S , (S [ i ]) ∈ 𝜸₀ (k ∷ ks)
    † (inl q) = let
                 ‡ : Σ i ꞉ index S , (S [ i ]) ∈ ↑[ 𝓓 ] β k
                   → ∃ i ꞉ index S , (S [ i ]) ∈ 𝜸₀ (k ∷ ks)
                 ‡ = λ { (i , p) → ∣ i , ∣ inl p ∣ ∣ }
                in
                 ∥∥-rec ∃-is-prop ‡ (ι (S , δ) q)
    † (inr q) = let
                 IH : ∃ i ꞉ index S , (S [ i ]) ∈ 𝜸₀ ks
                 IH = 𝜸₀-is-inaccessible-by-directed-joins ks (S , δ) q

                 ‡ : Σ i ꞉ index S , (S [ i ]) ∈ 𝜸₀ ks
                   → ∃ i ꞉ index S , (S [ i ]) ∈ 𝜸₀ (k ∷ ks)
                 ‡ = λ { (i , r) → ∣ i , ∣ inr r ∣ ∣ }
                in
                 ∥∥-rec ∃-is-prop ‡ IH

 𝜸₀-gives-scott-opens : (ks : List B)
                              → is-scott-open (𝜸₀ ks) holds
 𝜸₀-gives-scott-opens ks = ⦅𝟏⦆ , ⦅𝟐⦆
  where
   ⦅𝟏⦆ = 𝜸₀-is-upwards-closed ks
   ⦅𝟐⦆ = 𝜸₀-is-inaccessible-by-directed-joins ks

 𝜸₀-lemma : (x : ⟨ 𝓓 ⟩∙) (ks : List B)
                  → x ∈ 𝜸₀ ks → ∃ k ꞉ B , member k ks × β k ⊑⟨ 𝓓 ⟩ x
 𝜸₀-lemma x []       = λ ()
 𝜸₀-lemma x (k ∷ ks) p = ∥∥-rec ∃-is-prop † p
  where
   † : principal-filter 𝓓 (β k) x holds + x ∈ 𝜸₀ ks
     → ∃ k₀ ꞉ B , member k₀ (k ∷ ks) × underlying-order 𝓓 (β k₀) x
   † (inl q) = ∣ k , (in-head , q) ∣
   † (inr q) = ∥∥-rec
                ∃-is-prop
                (λ { (k₀ , r , s) → ∣ k₀ , in-tail r , s ∣ })
                (𝜸₀-lemma x ks q)

\end{code}

\begin{code}

 γ : List B → ⟨ 𝒪 Σ[𝓓] ⟩
 γ ks = 𝜸₀ ks , 𝜸₀-gives-scott-opens ks

 𝜸₁ : List B → ⟨ 𝒪 Σ[𝓓] ⟩
 𝜸₁ []       = 𝟎[ 𝒪 Σ[𝓓] ]
 𝜸₁ (k ∷ ks) = ↑ˢ[ (β k , ϟ k) ] ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ ks

\end{code}

\begin{code}

 γ-below-𝜸₁ : (bs : List B) → (γ bs ≤[ poset-of (𝒪 Σ[𝓓]) ] 𝜸₁ bs) holds
 γ-below-𝜸₁ []       _ ()
 γ-below-𝜸₁ (i ∷ is) j p =
  ∥∥-rec (holds-is-prop (𝜸₁ (i ∷ is) .pr₁ (β j))) † p
   where
    IH : (γ is ≤[ poset-of (𝒪 Σ[𝓓]) ] 𝜸₁ is) holds
    IH = γ-below-𝜸₁ is

    † : (β i ⊑⟨ 𝓓 ⟩ β j) + (β j ∈ₛ γ is) holds
      → ((β j) ∈ₛ 𝜸₁ (i ∷ is)) holds
    † (inl q) = ∣ inl ⋆ , q      ∣
    † (inr q) = ∣ inr ⋆ , IH j q ∣

 𝜸₁-below-γ : (bs : List B) → (𝜸₁ bs ≤[ poset-of (𝒪 Σ[𝓓]) ] γ bs) holds
 𝜸₁-below-γ []       j p = 𝟎-is-bottom (𝒪 Σ[𝓓]) (γ []) j p
 𝜸₁-below-γ (i ∷ is) j p = ∥∥-rec (holds-is-prop (β j ∈ₛ γ (i ∷ is))) † p
  where
   IH : (𝜸₁ is ≤[ poset-of (𝒪 Σ[𝓓]) ] γ is) holds
   IH = 𝜸₁-below-γ is

   † : (Σ k ꞉ 𝟚 𝓤 ,
         (β j ∈ₛ (⁅ ↑ˢ[ (β i , ϟ i ) ] , 𝜸₁ is ⁆ [ k ])) holds)
     → (β j ∈ₛ γ (i ∷ is)) holds
   † (inl ⋆ , r) = ∣ inl r        ∣
   † (inr ⋆ , r) = ∣ inr (IH j r) ∣

 γ-equal-to-𝜸₁ : (bs : List B) → γ bs ＝ 𝜸₁ bs
 γ-equal-to-𝜸₁ bs =
  ≤-is-antisymmetric (poset-of (𝒪 Σ[𝓓])) (γ-below-𝜸₁ bs) (𝜸₁-below-γ bs)

\end{code}

\begin{code}

 γ-lemma₁ : (is js : List B) → (γ is ≤[ poset-of (𝒪 Σ[𝓓]) ] γ (is ++ js)) holds
 γ-lemma₁ []       js       = λ _ ()
 γ-lemma₁ (i ∷ is) []       = let
                               open PosetNotation (poset-of (𝒪 Σ[𝓓]))

                               † : (i ∷ is) ＝ (i ∷ is) ++ []
                               † = []-right-neutral (i ∷ is)

                               ‡ : (γ (i ∷ is) ≤ γ (i ∷ is)) holds
                               ‡ = ≤-is-reflexive (poset-of (𝒪 Σ[𝓓])) (γ (i ∷ is))
                              in
                               transport (λ - → (γ (i ∷ is) ≤ γ -) holds) † ‡
 γ-lemma₁ (i ∷ is) (j ∷ js) x p = Ⅲ x (Ⅱ x (Ⅰ x p))
   where
    † : (𝜸₁ is ≤[ poset-of (𝒪 Σ[𝓓]) ] 𝜸₁ (is ++ (j ∷ js))) holds
    † y q =
     γ-below-𝜸₁ (is ++ (j ∷ js)) y (γ-lemma₁ is (j ∷ js) y (𝜸₁-below-γ is y q))

    Ⅰ = γ-below-𝜸₁ (i ∷ is)
    Ⅱ = ∨[ 𝒪 Σ[𝓓] ]-right-monotone †
    Ⅲ = 𝜸₁-below-γ (i ∷ (is ++ (j ∷ js)))

 γ-lemma₂ : (is js : List B) → (γ js ≤[ poset-of (𝒪 Σ[𝓓]) ] γ (is ++ js)) holds
 γ-lemma₂    []        js = ≤-is-reflexive (poset-of (𝒪 Σ[𝓓])) (γ js)
 γ-lemma₂ is@(i ∷ is′) js = λ x p → ∣_∣ (inr (γ-lemma₂ is′ js x p))

 γ-maps-∨-to-++ : (is js : List B) → 𝜸₁ (is ++ js) ＝ 𝜸₁ is ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ js
 γ-maps-∨-to-++ []       js = 𝟎-right-unit-of-∨ (𝒪 Σ[𝓓]) (𝜸₁ js) ⁻¹
 γ-maps-∨-to-++ (i ∷ is) js =
  𝜸₁ ((i ∷ is) ++ js)                                  ＝⟨ refl ⟩
  ↑ˢ[ β i , ϟ i ] ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ (is ++ js)              ＝⟨ Ⅰ    ⟩
  ↑ˢ[ β i , ϟ i ] ∨[ 𝒪 Σ[𝓓] ] (𝜸₁ is ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ js)    ＝⟨ Ⅱ    ⟩
  (↑ˢ[ β i , ϟ i ] ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ is) ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ js    ＝⟨ refl ⟩
  𝜸₁ (i ∷ is) ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ js                          ∎
   where
    Ⅰ = ap (λ - → ↑ˢ[ β i , ϟ i ] ∨[ 𝒪 Σ[𝓓] ] -) (γ-maps-∨-to-++ is js)
    Ⅱ = ∨[ 𝒪 Σ[𝓓] ]-assoc ↑ˢ[ β i , ϟ i ] (𝜸₁ is) (𝜸₁ js) ⁻¹

\end{code}

\begin{code}

 principal-filter-is-compact₀ : (c : ⟨ 𝓓 ⟩∙)
                              → (κ : is-compact 𝓓 c)
                              → is-compact-open Σ[𝓓] ↑ˢ[ (c , κ) ] holds
 principal-filter-is-compact₀ c κ S δ p = ∥∥-rec ∃-is-prop † q
  where
   q : (c ∈ₛ (⋁[ 𝒪 Σ[𝓓] ] S)) holds
   q = ⊆ₖ-implies-⊆ₛ ↑ˢ[ (c , κ) ] (⋁[ 𝒪 Σ[𝓓] ] S) p c (reflexivity 𝓓 c)

   † : Σ i ꞉ index S , (c ∈ₛ (S [ i ])) holds
     → ∃ i ꞉ index S , (↑ˢ[ (c , κ) ] ≤[ poset-of (𝒪 Σ[𝓓]) ] S [ i ]) holds
   † (i , r) = ∣ i , ‡ ∣
    where
     ‡ :  (↑ˢ[ c , κ ] ≤[ poset-of (𝒪 Σ[𝓓]) ] (S [ i ])) holds
     ‡ d = upward-closure (S [ i ]) c (β d) r

 principal-filter-is-compact : (b : B)
                             → is-compact-open Σ[𝓓] ↑ˢ[ (β b , ϟ b) ] holds
 principal-filter-is-compact b S δ p = ∥∥-rec ∃-is-prop † q
  where
   q : (β b ∈ₛ (⋁[ 𝒪 Σ[𝓓] ] S)) holds
   q = p b (reflexivity 𝓓 (β b))

   † : Σ k ꞉ index S , (β b ∈ₛ (S [ k ])) holds
     → ∃ i ꞉ index S , ((↑ˢ[ β b , ϟ b ]) ≤[ poset-of (𝒪 Σ[𝓓]) ] (S [ i ])) holds
   † (k , φ) = ∣ k , ‡ ∣
    where
     Sₖᴿ : 𝒪ₛᴿ
     Sₖᴿ = to-𝒪ₛᴿ (S [ k ])

     ‡ : (↑ˢ[ β b , ϟ b ] ≤[ poset-of (𝒪 Σ[𝓓]) ] (S [ k ])) holds
     ‡ d r = 𝒪ₛᴿ.pred-is-upwards-closed Sₖᴿ (β b) (β d) φ r

\end{code}

\begin{code}

 𝜸₁-gives-compact-opens : (b⃗ : List B) → is-compact-open Σ[𝓓] (𝜸₁ b⃗) holds
 𝜸₁-gives-compact-opens []       = 𝟎-is-compact Σ[𝓓]
 𝜸₁-gives-compact-opens (b ∷ bs) = †
  where
   𝔘ᶜ : ⟨ 𝒪 Σ[𝓓] ⟩
   𝔘ᶜ = ↑[ 𝓓 ] (β b)
      , compact-implies-principal-filter-is-scott-open (β b) (basis-is-compact b)

   b-compact : is-compact-open Σ[𝓓] 𝔘ᶜ holds
   b-compact = principal-filter-is-compact b

   𝔘ᶜᵣ : 𝒪ₛᴿ
   𝔘ᶜᵣ = to-𝒪ₛᴿ 𝔘ᶜ

   IH : is-compact-open Σ[𝓓] (𝜸₁ bs) holds
   IH = 𝜸₁-gives-compact-opens bs

   † : is-compact-open Σ[𝓓] (𝜸₁ (b ∷ bs)) holds
   † = compact-opens-are-closed-under-∨ Σ[𝓓] 𝔘ᶜ (𝜸₁ bs) b-compact IH

 γ-gives-compact-opens : (bs : List B) → is-compact-open Σ[𝓓] (γ bs) holds
 γ-gives-compact-opens bs =
  transport (λ - → is-compact-open Σ[𝓓] - holds) (γ-equal-to-𝜸₁ bs ⁻¹) †
   where
    † : is-compact-open Σ[𝓓] (𝜸₁ bs) holds
    † = 𝜸₁-gives-compact-opens bs

\end{code}

\begin{code}

 sup-is-compact : (c d s : ⟨ 𝓓 ⟩∙)
                → (κᶜ : is-compact 𝓓 c)
                → (κᵈ : is-compact 𝓓 d)
                → is-sup (underlying-order 𝓓) s (binary-family 𝓤 c d [_])
                → is-compact 𝓓 s
 sup-is-compact c d s κᶜ κᵈ (p , q) =
  binary-join-is-compact 𝓓 (p (inl ⋆)) (p (inr ⋆)) η κᶜ κᵈ
   where
    η : (d₁ : ⟨ 𝓓 ⟩∙) →
         underlying-order 𝓓 (binary-family 𝓤 c d [ inl ⋆ ]) d₁ →
         underlying-order 𝓓 (binary-family 𝓤 c d [ inr ⋆ ]) d₁ →
         underlying-order 𝓓 s d₁
    η d₁ r₁ r₂ = q d₁ λ { (inl ⋆) → r₁ ; (inr ⋆) → r₂ }

 open DefnOfScottLocale 𝓓 𝓤 pe using (_⊆ₛ_)

 principal-filter-reflects-joins : (c d s : ⟨ 𝓓 ⟩∙)
                                 → (κᶜ : is-compact 𝓓 c)
                                 → (κᵈ : is-compact 𝓓 d)
                                 → (σ : is-sup (underlying-order 𝓓) s (binary-family 𝓤 c d [_]))
                                 →
                                   let
                                    κˢ = sup-is-compact c d s κᶜ κᵈ σ
                                   in
                                    ↑ˢ[ s , κˢ ] ＝ ↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ]
 principal-filter-reflects-joins c d s κᶜ κᵈ σ =
  ≤-is-antisymmetric (poset-of (𝒪 Σ[𝓓])) Ⅰ Ⅱ
   where
    open PosetReasoning (poset-of (𝒪 Σ[𝓓]))

    κₛ : is-compact 𝓓 s
    κₛ = sup-is-compact c d s κᶜ κᵈ σ

    † : (↑ˢ[ s , κₛ ] ⊆ₛ (↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ])) holds
    † x p = (c ⊑⟨ 𝓓 ⟩[ pr₁ σ (inl ⋆) ] s ⊑⟨ 𝓓 ⟩[ p ] x ∎⟨ 𝓓 ⟩)
          , (d ⊑⟨ 𝓓 ⟩[ pr₁ σ (inr ⋆) ] s ⊑⟨ 𝓓 ⟩[ p ] x ∎⟨ 𝓓 ⟩)

    ‡ : ((↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ]) ⊆ₛ ↑ˢ[ s , κₛ ]) holds
    ‡ x (p , q) = pr₂ σ x λ { (inl ⋆) → p ; (inr ⋆) → q }

    Ⅰ : (↑ˢ[ s , κₛ ] ⊆ₖ (↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ])) holds
    Ⅰ = ⊆ₛ-implies-⊆ₖ ↑ˢ[ s , κₛ ] (↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ]) †

    Ⅱ : ((↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ]) ⊆ₖ ↑ˢ[ s , κₛ ]) holds
    Ⅱ = ⊆ₛ-implies-⊆ₖ (↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ]) ↑ˢ[ s , κₛ ] ‡

\end{code}

\begin{code}

 open BottomLemma 𝓓 𝕒 hl

 ↑ᵏ[_] : B →  ⟨ 𝒪 Σ[𝓓] ⟩
 ↑ᵏ[ i ] = ↑ˢ[ β i , ϟ i ]

 ⊤-is-compact : is-compact-open Σ[𝓓] 𝟏[ 𝒪 Σ[𝓓] ] holds
 ⊤-is-compact = transport (λ - → is-compact-open Σ[𝓓] - holds) ↑⊥-is-top †
  where
   † : is-compact-open ScottLocale ↑ˢ[ ⊥ᴰ , ⊥κ ] holds
   † = principal-filter-is-compact₀ ⊥ᴰ ⊥κ

 not-bounded-lemma : (c d : ⟨ 𝓓 ⟩∙)
                   → (κᶜ : is-compact 𝓓 c)
                   → (κᵈ : is-compact 𝓓 d)
                   → ¬ ((c ↑[ 𝓓 ] d) holds)
                   → ↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ] ＝ 𝟎[ 𝒪 Σ[𝓓] ]
 not-bounded-lemma c d κᶜ κᵈ ν =
  only-𝟎-is-below-𝟎 (𝒪 Σ[𝓓]) (↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ]) †
   where
    † : ((↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ]) ⊆ₖ 𝟎[ 𝒪 Σ[𝓓] ]) holds
    † i (p₁ , p₂) = 𝟘-elim (ν ∣ β i , (λ { (inl ⋆) → p₁ ; (inr ⋆) → p₂ }) ∣)

 γ-closure-under-∧₁ : (i : B) (is : List B)
                    → ∃ ks ꞉ List B , 𝜸₁ ks ＝ ↑ˢ[ β i , ϟ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ is
 γ-closure-under-∧₁ i [] = ∣ [] , (𝟎-right-annihilator-for-∧ (𝒪 Σ[𝓓]) ↑ˢ[ β i , ϟ i ] ⁻¹) ∣
 γ-closure-under-∧₁ i (j ∷ js) = cases †₁ †₂ (dc (β i) (β j))
  where
   IH : ∃ ks′ ꞉ List B , 𝜸₁ ks′ ＝ ↑ˢ[ β i , ϟ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
   IH = γ-closure-under-∧₁ i js

   †₁ : (β i ↑[ 𝓓 ] β j) holds
      → ∃ ks ꞉ List B , 𝜸₁ ks ＝ ↑ˢ[ β i , ϟ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ (j ∷ js)
   †₁ υ = ∥∥-rec ∃-is-prop ‡₁ ξ
    where
     open Joins (λ x y → x ⊑⟨ 𝓓 ⟩ₚ y)

     s : ⟨ 𝓓 ⟩∙
     s = pr₁ (bc ⁅ β i , β j ⁆ υ)

     φ : (s is-an-upper-bound-of ⁅ β i , β j ⁆) holds
     φ = pr₁ (pr₂ (bc ⁅ β i , β j ⁆ υ))

     ψ : is-lowerbound-of-upperbounds (underlying-order 𝓓) s (⁅ β i , β j ⁆ [_])
     ψ = pr₂ (pr₂ (bc ⁅ β i , β j ⁆ υ))

     κˢ : is-compact 𝓓 s
     κˢ = sup-is-compact (β i) (β j) s (ϟ i) (ϟ j) (φ , ψ)

     ξ : ∃ k ꞉ B , β k ＝ s
     ξ = small-compact-basis-contains-all-compact-elements 𝓓 β scb s κˢ

     ‡₁ : Σ k ꞉ B , β k ＝ s
        → ∃ ks ꞉ List B , 𝜸₁ ks ＝ ↑ˢ[ β i , ϟ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ (j ∷ js)
     ‡₁ (k , p) = ∥∥-rec ∃-is-prop ※₁ IH
      where
       ※₁ : Σ ks′ ꞉ List B , 𝜸₁ ks′ ＝ ↑ˢ[ β i , ϟ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
          → ∃ ks ꞉ List B , 𝜸₁ ks ＝ ↑ˢ[ β i , ϟ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ (j ∷ js)
       ※₁ (ks′ , q) = ∣ (k ∷ ks′) , ♣ ∣
        where
         μ : ↑ᵏ[ k ] ＝ ↑ˢ[ s , κˢ ]
         μ = to-subtype-＝ (holds-is-prop ∘ is-scott-open) (ap (λ - → ↑[ 𝓓 ] -) p)

         ρ : ↑ᵏ[ k ] ＝ ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] ↑ᵏ[ j ]
         ρ = ↑ᵏ[ k ]      ＝⟨ μ ⟩
             ↑ˢ[ s , κˢ ] ＝⟨ (principal-filter-reflects-joins (β i) (β j) s (ϟ i) (ϟ j) (φ , ψ)) ⟩
             ↑ˢ[ β i , ϟ i ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ β j , ϟ j ] ∎

         Ⅰ = ap (λ - → - ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ ks′) ρ
         Ⅱ = ap (λ - → (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] ↑ᵏ[ j ]) ∨[ 𝒪 Σ[𝓓] ] -) q
         Ⅲ = binary-distributivity (𝒪 Σ[𝓓]) ↑ᵏ[ i ] ↑ᵏ[ j ] (𝜸₁ js) ⁻¹

         ♣ : 𝜸₁ (k ∷ ks′) ＝ ↑ˢ[ β i , ϟ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ (j ∷ js)
         ♣ = 𝜸₁ (k ∷ ks′)                                                    ＝⟨ refl ⟩
             ↑ᵏ[ k ] ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ ks′                                        ＝⟨ Ⅰ ⟩
             (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] ↑ᵏ[ j ]) ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ ks′                    ＝⟨ Ⅱ ⟩
             (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] ↑ᵏ[ j ]) ∨[ 𝒪 Σ[𝓓] ] (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js) ＝⟨ Ⅲ ⟩
             ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] (↑ᵏ[ j ] ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ js)                     ＝⟨ refl ⟩
             ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ (j ∷ js)                                   ∎

   †₂ : ¬ ((β i ↑[ 𝓓 ] β j) holds)
      → ∃ ks ꞉ List B , 𝜸₁ ks ＝ ↑ˢ[ β i , ϟ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ (j ∷ js)
   †₂ ν = ∥∥-rec ∃-is-prop ‡₂ IH
    where
     ‡₂ : Σ ks′ ꞉ List B , 𝜸₁ ks′ ＝ ↑ˢ[ β i , ϟ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
        → ∃ ks ꞉ List B , 𝜸₁ ks ＝ ↑ˢ[ β i , ϟ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ (j ∷ js)
     ‡₂ (ks′ , p) = ∣ ks′ , ρ ∣
      where
       ρ : 𝜸₁ ks′ ＝  ↑ˢ[ β i , ϟ i ] ∧[ 𝒪 Σ[𝓓] ] (𝜸₁ (j ∷ js))
       ρ =
        𝜸₁ ks′                                                          ＝⟨ p    ⟩
        ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js                                         ＝⟨ Ⅰ    ⟩
        𝟎[ 𝒪 Σ[𝓓] ] ∨[ 𝒪 Σ[𝓓] ] (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js)                   ＝⟨ Ⅱ    ⟩
        (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] ↑ᵏ[ j ]) ∨[ 𝒪 Σ[𝓓] ] (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js) ＝⟨ Ⅲ    ⟩
        ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] (↑ᵏ[ j ] ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ js)                     ＝⟨ refl ⟩
        ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ (j ∷ js)                                   ∎
         where
          Ⅰ = 𝟎-right-unit-of-∨ (𝒪 Σ[𝓓]) (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js) ⁻¹
          Ⅱ = ap
               (λ - → - ∨[ 𝒪 Σ[𝓓] ] (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js))
               (not-bounded-lemma (β i) (β j) (ϟ i) (ϟ j) ν ⁻¹ )
          Ⅲ = binary-distributivity (𝒪 Σ[𝓓]) ↑ᵏ[ i ] ↑ᵏ[ j ] (𝜸₁ js) ⁻¹

 γ-closure-under-∧ : (is js : List B)
                   → ∃ ks ꞉ List B , 𝜸₁ ks ＝ 𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
 γ-closure-under-∧ []       js = ∣ [] , (𝟎-left-annihilator-for-∧ (𝒪 Σ[𝓓]) (𝜸₁ js) ⁻¹) ∣
 γ-closure-under-∧ (i ∷ is) js = ∥∥-rec₂ ∃-is-prop † η₀ ρ₀
  where
   η₀ : ∃ ks₀ ꞉ List B , 𝜸₁ ks₀ ＝ 𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
   η₀ = γ-closure-under-∧ is js

   ρ₀ : ∃ ks₁ ꞉ List B , 𝜸₁ ks₁ ＝ ↑ˢ[ β i , ϟ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
   ρ₀ = γ-closure-under-∧₁ i js

   † : Σ ks₀ ꞉ List B , 𝜸₁ ks₀ ＝ 𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
     → Σ ks₁ ꞉ List B , 𝜸₁ ks₁ ＝ ↑ˢ[ β i , ϟ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
     → ∃ ks ꞉ List B , 𝜸₁ ks ＝ 𝜸₁ (i ∷ is) ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
   † (ks₀ , p₀) (ks₁ , p₁) = ∣ (ks₀ ++ ks₁) , ‡ ∣
    where
     ‡ : 𝜸₁ (ks₀ ++ ks₁) ＝ 𝜸₁ (i ∷ is) ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
     ‡ =
      𝜸₁ (ks₀ ++ ks₁)                                                     ＝⟨ Ⅰ ⟩
      𝜸₁ ks₀ ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ ks₁                                             ＝⟨ Ⅱ    ⟩
      (𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js) ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ ks₁                            ＝⟨ Ⅲ    ⟩
      (𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js) ∨[ 𝒪 Σ[𝓓] ] (↑ˢ[ β i , ϟ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js) ＝⟨ Ⅳ    ⟩
      (𝜸₁ is ∨[ 𝒪 Σ[𝓓] ] ↑ˢ[ β i , ϟ i ]) ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js                   ＝⟨ Ⅴ    ⟩
      (↑ˢ[ β i , ϟ i ] ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ is) ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js                   ＝⟨ refl ⟩
      𝜸₁ (i ∷ is) ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js                                         ∎
       where
        Ⅰ = γ-maps-∨-to-++ ks₀ ks₁
        Ⅱ = ap (λ - → - ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ ks₁) p₀
        Ⅲ = ap (λ - → (𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js) ∨[ 𝒪 Σ[𝓓] ] -) p₁
        Ⅳ = binary-distributivity-right (𝒪 Σ[𝓓]) ⁻¹
        Ⅴ = ap
             (λ - → - ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js)
             (∨[ 𝒪 Σ[𝓓] ]-is-commutative (𝜸₁ is) ↑ᵏ[ i ])

\end{code}

\begin{code}

 basis-for-Σ[𝓓] : Fam 𝓤 ⟨ 𝒪 Σ[𝓓] ⟩
 basis-for-Σ[𝓓] = List B , γ

 open PropertiesAlgebraic 𝓓 𝕒

 Σ[𝓓]-dir-basis-forᴰ : directed-basis-forᴰ (𝒪 Σ[𝓓]) basis-for-Σ[𝓓]
 Σ[𝓓]-dir-basis-forᴰ U@(_ , so) = (D , δ) , † , 𝒹
   where
    open Joins (λ x y → x ≤[ poset-of (𝒪 Σ[𝓓]) ] y)

    Uᴿ : 𝒪ₛᴿ
    Uᴿ = to-𝒪ₛᴿ U

    open 𝒪ₛᴿ Uᴿ renaming (pred to 𝔘)

    D : 𝓤  ̇
    D = (Σ b⃗ ꞉ (List B) , ((b : B) → member b b⃗ → (β b) ∈ 𝔘))

    δ : (Σ b⃗ ꞉ (List B) , ((b : B) → member b b⃗ → (β b) ∈ 𝔘)) → List B
    δ = pr₁

    †₁ : (U is-an-upper-bound-of ⁅ γ d ∣ d ε (D , δ) ⁆) holds
    †₁ (b⃗ , r) b p =
     ∥∥-rec (holds-is-prop (β b ∈ₚ 𝔘)) ‡₁ (𝜸₀-lemma (β b) b⃗ p)
      where
       ‡₁ : Σ k ꞉ B , member k b⃗ × β k ⊑⟨ 𝓓 ⟩ β b → β b ∈ 𝔘
       ‡₁ (k , q , φ) = pred-is-upwards-closed (β k) (β b) (r k q) φ

    †₂ : ((U′ , _) : upper-bound ⁅ γ d ∣ d ε (D , δ) ⁆)
       → (U ≤[ poset-of (𝒪 Σ[𝓓]) ] U′) holds
    †₂ (U′ , ψ) k p = ‡₂ k (reflexivity 𝓓 (β k))
     where
      r : ↑ˢ[ β k , ϟ k ] ＝ γ (k ∷ [])
      r =
       ↑ˢ[ β k , ϟ k ]                         ＝⟨ Ⅰ ⟩
       ↑ˢ[ β k , ϟ k ] ∨[ 𝒪 Σ[𝓓] ] 𝟎[ 𝒪 Σ[𝓓] ]     ＝⟨ Ⅱ ⟩
       γ (k ∷ [])                              ∎
        where
         Ⅰ = 𝟎-left-unit-of-∨ (𝒪 Σ[𝓓]) ↑ˢ[ β k , ϟ k ] ⁻¹
         Ⅱ = γ-equal-to-𝜸₁ (k ∷ []) ⁻¹

      ‡₂ : (↑ˢ[ β k , ϟ k ] ≤[ poset-of (𝒪 Σ[𝓓]) ] U′) holds
      ‡₂ = transport
            (λ - → (- ≤[ poset-of (𝒪 Σ[𝓓]) ] U′) holds)
            (r ⁻¹)
            (ψ ((k ∷ []) , λ { _ in-head → p }))

    † : (U is-lub-of ⁅ γ d ∣ d ε (D , δ) ⁆) holds
    † = †₁ , †₂

    𝒹↑ : ((is , _) (js , _) : D)
       → ∃ (ks , _) ꞉ D ,
            (γ is ≤[ poset-of (𝒪 Σ[𝓓]) ] γ ks) holds
          × (γ js ≤[ poset-of (𝒪 Σ[𝓓]) ] γ ks) holds
    𝒹↑ (is , 𝕚) (js , 𝕛)= ∣ ((is ++ js) , ♣) , γ-lemma₁ is js , γ-lemma₂ is js ∣
     where
      ♣ : (b : B) → member b (is ++ js) → 𝔘 (β b) holds
      ♣ b q = cases (𝕚 b) (𝕛 b) (member-in-++ is js b q)

    𝒹 : is-directed (𝒪 Σ[𝓓]) (⁅ γ d ∣ d ε (D , δ) ⁆) holds
    𝒹 = ∣ [] , (λ _ ()) ∣ , 𝒹↑

 σᴰ : spectralᴰ Σ[𝓓]
 σᴰ = pr₁ Σ-assoc (𝒷 , (γ-gives-compact-opens , τ , μ))
  where
   𝒷 : directed-basisᴰ (𝒪 Σ[𝓓])
   𝒷 = basis-for-Σ[𝓓] , Σ[𝓓]-dir-basis-forᴰ

   τ : contains-top (𝒪 Σ[𝓓]) basis-for-Σ[𝓓] holds
   τ = ∥∥-rec
        (holds-is-prop (contains-top (𝒪 Σ[𝓓]) basis-for-Σ[𝓓]))
        †
        (compact-opens-are-basic Σ[𝓓] 𝒷 𝟏[ 𝒪 Σ[𝓓] ] ⊤-is-compact)
    where
     † : Σ is ꞉ List B , (γ is) ＝ 𝟏[ 𝒪 Σ[𝓓] ]
       → contains-top (𝒪 Σ[𝓓]) basis-for-Σ[𝓓] holds
     † (is , p) =
      ∣ is , transport (λ - → is-top (𝒪 Σ[𝓓]) - holds) (p ⁻¹) (𝟏-is-top (𝒪 Σ[𝓓])) ∣

   μ : closed-under-binary-meets (𝒪 Σ[𝓓]) basis-for-Σ[𝓓] holds
   μ is js = ∥∥-rec ∃-is-prop † (γ-closure-under-∧ is js)
    where
     open Meets (λ x y → x ≤[ poset-of (𝒪 Σ[𝓓]) ] y)

     † : (Σ ks ꞉ List B , 𝜸₁ ks ＝ 𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js)
       → ∃ ks ꞉ List B , ((γ ks) is-glb-of (γ is , γ js)) holds
     † (ks , p) =
      ∣ ks , transport (λ - → (- is-glb-of (γ is , γ js)) holds) q ‡ ∣
       where
        q : γ is ∧[ 𝒪 Σ[𝓓] ] γ js ＝ γ ks
        q = γ  is ∧[ 𝒪 Σ[𝓓] ] γ  js      ＝⟨ Ⅰ ⟩
            𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] γ  js      ＝⟨ Ⅱ ⟩
            𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js      ＝⟨ Ⅲ ⟩
            𝜸₁ ks                      ＝⟨ Ⅳ ⟩
            γ ks                       ∎
             where
              Ⅰ = ap (λ - → -     ∧[ 𝒪 Σ[𝓓] ] γ js) (γ-equal-to-𝜸₁ is)
              Ⅱ = ap (λ - → 𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] -   ) (γ-equal-to-𝜸₁ js)
              Ⅲ = p ⁻¹
              Ⅳ = γ-equal-to-𝜸₁ ks ⁻¹

        ‡ : ((γ is ∧[ 𝒪 Σ[𝓓] ] γ js) is-glb-of (γ is , γ js)) holds
        ‡ = (∧[ 𝒪 Σ[𝓓] ]-lower₁ (γ is) (γ js) , ∧[ 𝒪 Σ[𝓓] ]-lower₂ (γ is) (γ js))
          , λ { (l , φ , ψ) → ∧[ 𝒪 Σ[𝓓] ]-greatest (γ is) (γ js) l φ ψ }

\end{code}
