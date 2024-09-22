---
title:         Properties of the way-below relation
author:        Ayberk Tosun
date-started:  2023-08-19
dates-updated: [2024-09-12]
---

The module contains properties of the way below relation defined in
`Locales.WayBelowRelation.Definition`.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt
open import MLTT.Spartan
open import UF.Logic
open import UF.SubtypeClassifier
open import Slice.Family

module Locales.WayBelowRelation.Properties (pt : propositional-truncations-exist)
                                           (fe : Fun-Ext) where

open import Locales.WayBelowRelation.Definition pt fe

open import Locales.Frame pt fe

open PropositionalTruncation pt

open AllCombinators pt fe
open Locale

\end{code}

The bottom open `𝟎` is way below anything.

\begin{code}

𝟎-is-way-below-anything : (X : Locale 𝓤 𝓥 𝓦)
                        → (U : ⟨ 𝒪 X ⟩) → (𝟎[ 𝒪 X ] ≪[ 𝒪 X ] U) holds
𝟎-is-way-below-anything X U S (ι , _) p = ∥∥-rec ∃-is-prop † ι
 where
  † : index S → ∃ i ꞉ index S , (𝟎[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] S [ i ]) holds
  † i = ∣ i , 𝟎-is-bottom (𝒪 X) (S [ i ]) ∣

\end{code}

Added on 2024-09-12.

\begin{code}

way-below-implies-below : (X : Locale 𝓤 𝓥 𝓦)
                        → {U V : ⟨ 𝒪 X ⟩}
                        → (U ≪[ 𝒪 X ] V ⇒ U ≤[ poset-of (𝒪 X) ] V) holds
way-below-implies-below {𝓤} {𝓥} {𝓦} X {U} {V} φ =
 ∥∥-rec (holds-is-prop (U ≤[ Xₚ ] V)) † (φ S δ p)
  where
   S : Fam 𝓦 ⟨ 𝒪 X ⟩
   S = 𝟙 , λ { ⋆ → V }

   Xₚ = poset-of (𝒪 X)

   γ : (i j : index S)
     → ∃ k ꞉ index S , (S [ i ] ≤[ Xₚ ] S [ k ]) holds
                     × (S [ j ] ≤[ Xₚ ] S [ k ]) holds
   γ ⋆ ⋆ = ∣ ⋆ , ≤-is-reflexive Xₚ V , ≤-is-reflexive Xₚ V ∣

   δ : is-directed (𝒪 X) S holds
   δ = ∣ ⋆ ∣ , γ

   p : (V ≤[ Xₚ ] (⋁[ 𝒪 X ] S)) holds
   p = ⋁[ 𝒪 X ]-upper S ⋆

   † : (Σ _ ꞉ 𝟙 , (U ≤[ Xₚ ] V) holds) → (U ≤[ Xₚ ] V) holds
   † (⋆ , p) = p

\end{code}

Added on 2024-09-12.

\begin{code}

↑↑-is-upward-closed
 : (X : Locale 𝓤 𝓥 𝓦)
 → {U V W : ⟨ 𝒪 X ⟩}
 → (U ≪[ 𝒪 X ] V ⇒ V ≤[ poset-of (𝒪 X) ] W ⇒ U ≪[ 𝒪 X ] W) holds
↑↑-is-upward-closed X {U} {V} {W} φ q = †
 where
  open PosetReasoning (poset-of (𝒪 X))

  † : (U ≪[ 𝒪 X ] W) holds
  † S δ r = φ S δ p
   where
    p : (V ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] S)) holds
    p = V ≤⟨ q ⟩ W ≤⟨ r ⟩ ⋁[ 𝒪 X ] S ■

\end{code}

Added on 2024-09-12.

\begin{code}

being-way-below-is-closed-under-binary-joins
 : (X : Locale 𝓤 𝓥 𝓦)
 → {U V W : ⟨ 𝒪 X ⟩}
 → (V ≪[ 𝒪 X ] U ⇒ W ≪[ 𝒪 X ] U ⇒ (V ∨[ 𝒪 X ] W) ≪[ 𝒪 X ] U) holds
being-way-below-is-closed-under-binary-joins X {U} {V} {W} p q S δ@(_ , υ) r =
 ∥∥-rec₂ ∃-is-prop γ (p S δ r) (q S δ r)
  where
   open PosetReasoning (poset-of (𝒪 X))

   † : (V ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] S)) holds
   † = way-below-implies-below X (↑↑-is-upward-closed X p r)

   ‡ : (W ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] S)) holds
   ‡ = way-below-implies-below X (↑↑-is-upward-closed X q r)

   Xₚ = poset-of (𝒪 X)

   γ : Σ i ꞉ index S , (V ≤[ Xₚ ] S [ i ]) holds
     → Σ i ꞉ index S , (W ≤[ Xₚ ] S [ i ]) holds
     → ∃ k ꞉ index S , ((V ∨[ 𝒪 X ] W) ≤[ Xₚ ] S [ k ]) holds
   γ (i , p) (j , q) = ∥∥-rec ∃-is-prop ε (υ i j)
    where
     ε : Σ k ꞉ index S ,
          (S [ i ] ≤[ Xₚ ] S [ k ] ∧ S [ j ] ≤[ Xₚ ] S [ k ]) holds
       → ∃ k ꞉ index S ,
          ((V ∨[ 𝒪 X ] W) ≤[ Xₚ ] S [ k ]) holds
     ε (k , r , s) = ∣ k , ∨[ 𝒪 X ]-least φ ψ ∣
      where
       φ : (V ≤[ poset-of (𝒪 X) ] (S [ k ])) holds
       φ = V ≤⟨ p ⟩ S [ i ] ≤⟨ r ⟩ S [ k ] ■

       ψ : (W ≤[ poset-of (𝒪 X) ] (S [ k ])) holds
       ψ = W ≤⟨ q ⟩ S [ j ] ≤⟨ s ⟩ S [ k ] ■

\end{code}
