---
title:        Points of formal topologies
author:       Ayberk Tosun
date-started: 2026-11-21
---

This module define the notion of point of a formal topology, sometimes called a
_formal point_.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module Locales.FormalTopology.Point
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Locales.FormalTopology.Definition pt fe
open import Locales.Frame pt fe hiding (⟨_⟩)
open import MLTT.Spartan
-- open import Notation.CanonicalMap
open import Notation.UnderlyingType
-- open import UF.Base
open import UF.Powerset
open import UF.Logic
open import UF.SubtypeClassifier
open import UF.Sets

-- open Formal-Topology-Morphism
-- open Quasi-Formal-Topology-Morphism
open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

\begin{code}

module Formal-Point (𝒜 : Formal-Topology 𝓤) where

 private
  P𝒜 = underlying-poset-of-formal-topology 𝒜

 is-inhabitedₚ : 𝓟 ⟨ 𝒜 ⟩ → Ω 𝓤
 is-inhabitedₚ U = is-inhabited U , being-inhabited-is-prop U
  where
   open inhabited-subsets pt

 is-upward-closed : 𝓟 ⟨ 𝒜 ⟩ → Ω 𝓤
 is-upward-closed U =
  Ɐ u ꞉ ⟨ 𝒜 ⟩ , u ∈ₚ U ⇒ (Ɐ a ꞉ ⟨ 𝒜 ⟩ , u ≤[ P𝒜 ] a ⇒ a ∈ₚ U)

 is-downward-directed : 𝓟 ⟨ 𝒜 ⟩ → Ω 𝓤
 is-downward-directed U =
  Ɐ u₁ u₂ ꞉ ⟨ 𝒜 ⟩ ,
   Ǝₚ u₃ ꞉ ⟨ 𝒜 ⟩ , (u₃ ∈ₚ U ∧ u₃ ≤[ P𝒜 ] u₁ ∧ u₂ ≤[ P𝒜 ] u₁)

 is-completely-prime-wrt-covering : 𝓟 ⟨ 𝒜 ⟩ → Ω (𝓤 ⁺)
 is-completely-prime-wrt-covering F =
  Ɐ a ꞉ ⟨ 𝒜 ⟩ ,
   Ɐ U ꞉ 𝓟 ⟨ 𝒜 ⟩ ,
    a ∈ₚ F ⇒
     a ◁[ 𝒜 ] U ⇒
      Ǝₚ u ꞉ ⟨ 𝒜 ⟩ , (u ∈ₚ U ∧ u ∈ₚ F)

\end{code}

\begin{code}

 is-formal-point : 𝓟 ⟨ 𝒜 ⟩ → Ω (𝓤 ⁺)
 is-formal-point F =
  is-inhabitedₚ F ∧ is-downward-directed F ∧ is-completely-prime-wrt-covering F

\end{code}

\begin{code}

 formal-point-is-upward-closed : (F : 𝓟 ⟨ 𝒜 ⟩)
                               → (is-formal-point F ⇒ is-upward-closed F) holds
 formal-point-is-upward-closed F (ι , δ , θ) x p a q = ∥∥-rec (holds-is-prop (F a)) γ †
  where
   σ : is-set ⟨ 𝒜 ⟩
   σ = carrier-of-formal-topology-is-set 𝒜

   P = underlying-poset-of-formal-topology 𝒜

   open singleton-subsets σ

   cov₁ : (a ◁[ 𝒜 ] ❴ a ❵) holds
   cov₁ =
    reflexivity-of-quasi-cover (underlying-quasi-formal-topology 𝒜) a ❴ a ❵ refl

   cov₂ : (x ◁[ 𝒜 ] ❴ a ❵) holds
   cov₂ = cover-satisfies-left-rule 𝒜 a x ❴ a ❵ q cov₁

   † : (Ǝₚ a′ ꞉ ⟨ 𝒜 ⟩ , (a′ ∈ₚ ❴ a ❵ ∧ a′ ∈ₚ F)) holds
   † = θ x ❴ a ❵ p cov₂

   γ : Σ a′ ꞉ ⟨ 𝒜 ⟩ , (a′ ∈ₚ ❴ a ❵ ∧ a′ ∈ₚ F) holds → a ∈ F
   γ (a′ , r , p′) = transport (λ - → (- ∈ₚ F) holds) (r ⁻¹) p′

\end{code}

[1]: Sara Negri. _Continuous domains as formal spaces_. Mathematical Structures
     in Computer Science, Volume 12, No. 1, pp. 19–52, 2002.
     DOI:10.1017/S0960129501003450
