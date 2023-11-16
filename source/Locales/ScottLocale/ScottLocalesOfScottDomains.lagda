---
title:       The spectral Scott locale of a Scott domain
author:      Ayberk Tosun
start-date:  2023-10-25
---

Ayberk Tosun.

Started on: 2023-10-25.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
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
open import UF.Equiv
open import UF.Embeddings

module Locales.ScottLocale.ScottLocalesOfScottDomains
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
        (𝓤  : Universe) where

open import DomainTheory.Basics.Dcpo                         pt fe 𝓤
 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Basics.Pointed                      pt fe 𝓤
 renaming (⊥ to ⊥d)
open import DomainTheory.Basics.WayBelow                     pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Bases            pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity       pt fe 𝓤
open import DomainTheory.BasesAndContinuity.CompactBasis     pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤
open import DomainTheory.Topology.ScottTopology              pt fe 𝓤
open import DomainTheory.Topology.ScottTopologyProperties    pt fe 𝓤
open import Locales.Frame                                    pt fe
 hiding (∅)

open import Locales.SmallBasis pt fe sr

open Universal fe
open Implication fe
open Existential pt
open Disjunction pt
open Conjunction
open PowersetOperations

open Locale

open PropositionalTruncation pt hiding (_∨_)

\end{code}

\begin{code}

module SpectralScottLocaleConstruction
        (𝓓    : DCPO {𝓤 ⁺} {𝓤})
        (hscb : has-specified-small-compact-basis 𝓓)
        (pe   : propext 𝓤) where

 open ScottLocaleConstruction 𝓓

\end{code}

We denote by `𝒮𝓓` the Scott locale of the dcpo `𝓓`.

\begin{code}

 𝒮𝓓 : Locale (𝓤 ⁺) 𝓤 𝓤
 𝒮𝓓 = ScottLocale hscb pe

\end{code}

We denote by `(B, β)` the algebraic basis of the pointed dcpo 𝓓.

\begin{code}

 B : 𝓤  ̇
 B = index-of-compact-basis 𝓓 hscb

 β : B → ⟨ 𝓓 ⟩∙
 β i = family-of-basic-opens 𝓓 hscb i

 open structurally-algebraic

 scb : is-small-compact-basis 𝓓 (family-of-basic-opens 𝓓 hscb)
 scb = small-compact-basis 𝓓 hscb

 open is-small-compact-basis scb

\end{code}

We define some nice notation for the prop-valued equality of the dcpo `𝓓`.

\begin{code}

 _＝ₚ_ : ⟨ 𝓓 ⟩∙ → ⟨ 𝓓 ⟩∙ → Ω (𝓤 ⁺)
 x ＝ₚ y = (x ＝ y) , sethood 𝓓

\end{code}

We now construct the basis for this locale.

\begin{code}

 open DefnOfScottTopology 𝓓 𝓤
 open Properties 𝓓

 open binary-unions-of-subsets pt

 from-list₀ : List B → 𝓟 {𝓤} {𝓤 ⁺} ⟨ 𝓓 ⟩∙
 from-list₀ = foldr _∪_ ∅ ∘ map (principal-filter 𝓓 ∘ β)

 from-list₀-is-upwards-closed : (ks : List B)
                              → is-upwards-closed (from-list₀ ks) holds
 from-list₀-is-upwards-closed []       x y () q
 from-list₀-is-upwards-closed (b ∷ bs) x y p  q =
  ∥∥-rec (holds-is-prop (y ∈ₚ from-list₀ (b ∷ bs))) † p
   where
    † : (β b ⊑⟨ 𝓓 ⟩ x) + x ∈ from-list₀ bs → from-list₀ (b ∷ bs) y holds
    † (inl r) = ∣ inl (principal-filter-is-upwards-closed (β b) x y r q) ∣
    † (inr r) = ∣ inr (from-list₀-is-upwards-closed bs x y r q) ∣

 from-list₀-is-inaccessible-by-directed-joins : (ks : List B)
                                             → is-inaccessible-by-directed-joins
                                                (from-list₀ ks)
                                                 holds
 from-list₀-is-inaccessible-by-directed-joins []       (S , δ) ()
 from-list₀-is-inaccessible-by-directed-joins (k ∷ ks) (S , δ) p =
  ∥∥-rec ∃-is-prop † p
   where
    σ : is-scott-open (↑[ 𝓓 ] β k) holds
    σ = compact-implies-principal-filter-is-scott-open (β k) (basis-is-compact k)

    υ : is-upwards-closed (↑[ 𝓓 ] (β k)) holds
    υ = 𝒪ₛᴿ.pred-is-upwards-closed (to-𝒪ₛᴿ (↑[ 𝓓 ] (β k) , σ))

    ι : is-inaccessible-by-directed-joins (↑[ 𝓓 ] β k) holds
    ι = 𝒪ₛᴿ.pred-is-inaccessible-by-dir-joins (to-𝒪ₛᴿ (↑[ 𝓓 ] (β k) , σ))

    † : (β k ⊑⟨ 𝓓 ⟩ (⋁ (S , δ))) + (⋁ (S , δ)) ∈ from-list₀ ks
      → ∃ i ꞉ index S , (S [ i ]) ∈ from-list₀ (k ∷ ks)
    † (inl q) = let
                 ‡ : Σ i ꞉ index S , (S [ i ]) ∈ ↑[ 𝓓 ] β k
                   → ∃ i ꞉ index S , (S [ i ]) ∈ from-list₀ (k ∷ ks)
                 ‡ = λ { (i , p) → ∣ i , ∣ inl p ∣ ∣ }
                in
                 ∥∥-rec ∃-is-prop ‡ (ι (S , δ) q)
    † (inr q) = let
                 IH : ∃ i ꞉ index S , (S [ i ]) ∈ from-list₀ ks
                 IH = from-list₀-is-inaccessible-by-directed-joins ks (S , δ) q

                 ‡ : Σ i ꞉ index S , (S [ i ]) ∈ from-list₀ ks
                   → ∃ i ꞉ index S , (S [ i ]) ∈ from-list₀ (k ∷ ks)
                 ‡ = λ { (i , r) → ∣ i , ∣ inr r ∣ ∣ }
                in
                 ∥∥-rec ∃-is-prop ‡ IH

 from-list₀-gives-scott-opens : (ks : List B)
                              → is-scott-open (from-list₀ ks) holds
 from-list₀-gives-scott-opens ks = ⦅𝟏⦆ , ⦅𝟐⦆
  where
   ⦅𝟏⦆ = from-list₀-is-upwards-closed ks
   ⦅𝟐⦆ = from-list₀-is-inaccessible-by-directed-joins ks

 from-list : List B → ⟨ 𝒪 𝒮𝓓 ⟩
 from-list ks = from-list₀ ks , from-list₀-gives-scott-opens ks

 basis-for-𝒮𝓓 : Fam 𝓤 ⟨ 𝒪 𝒮𝓓 ⟩
 basis-for-𝒮𝓓 = List B , from-list

 𝒮𝓓-dir-basis-forᴰ : directed-basis-forᴰ (𝒪 𝒮𝓓) basis-for-𝒮𝓓
 𝒮𝓓-dir-basis-forᴰ U = ({!!} , {!!}) , {!!}

 fun-fact : (ua : is-univalent 𝓤) (fe : funext 𝓤 (𝓤 ⁺))
          → (X : 𝓤  ̇)
          → Subtypes' 𝓤 X ≃ (X → Ω 𝓤)
 fun-fact ua fe X = Ω-is-subtype-classifier' {𝓤 = 𝓤} {𝓥 = 𝓤} ua fe X

 σᴰ : spectralᴰ 𝒮𝓓
 σᴰ = basis-for-𝒮𝓓 , 𝒮𝓓-dir-basis-forᴰ , ({!!} , (τ , μ))
  where
   τ : contains-top (𝒪 𝒮𝓓) basis-for-𝒮𝓓 holds
   τ = {!!}

   μ : closed-under-binary-meets (𝒪 𝒮𝓓) basis-for-𝒮𝓓 holds
   μ = {!!}

\end{code}
