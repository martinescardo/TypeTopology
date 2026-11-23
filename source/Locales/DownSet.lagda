---
title:  Downward-closed sets
author: Ayberk Tosun
date:   2026-11-20
---

The notion of down set is used in many places throughout the locale theory
development. In this module, we define it in its most general form to avoid
duplication. We also collect lemmas about it.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc

module Locales.DownSet
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.Frame pt fe hiding (⟨_⟩)
open import MLTT.Spartan
open import UF.Logic
open import UF.Powerset
open import UF.Subsingletons
open import UF.SubtypeClassifier

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

We define what it means for a subset `U` to be downward closed with respect to
some order `_≤_`. We do not assume anything about the order.

\begin{code}

is-downward-closed : {A : 𝓤  ̇} → (_≤_ : A → A → Ω 𝓥) → 𝓟' {𝓦} A → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
is-downward-closed {_} {_} {_} {A} _≤_ U =
 Ɐ u ꞉ A , u ∈ₚ U ⇒ (Ɐ a ꞉ A , a ≤ u ⇒ a ∈ₚ U)

\end{code}

By `Downward-Closed-Subset' 𝓦` we denote the type of `𝓦`-valued downward-closed
subsets.

\begin{code}

Downward-Closed-Subset' : (𝓦 : Universe)
                        → {A : 𝓤  ̇}
                        → (_≤_ : A → A → Ω 𝓥)
                        → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
Downward-Closed-Subset' {_} {_} 𝓦 {A} _≤_ =
 Σ U ꞉ 𝓟' {𝓦} A , is-downward-closed _≤_ U holds

\end{code}

In most cases, we work with down sets in the same as universe as that of the
type in consideration. We define a special case for this. Our use of the prime
symbol here follows the notational distinction between `𝓟` and `𝓟'` from the
`UF.Powerset` module.

\begin{code}

Downward-Closed-Subset : {A : 𝓤  ̇} → (_≤_ : A → A → Ω 𝓥) → 𝓤 ⁺ ⊔ 𝓥  ̇
Downward-Closed-Subset {𝓤} {_} {A} _≤_ = Downward-Closed-Subset' 𝓤 _≤_

\end{code}

We also define a special case that directly captures the downward-closed subsets
of a poset. This is denoted by `Downward-Closed-Subsetₚ`.

\begin{code}

Downward-Closed-Subsetₚ : (P : Poset 𝓤 𝓥) → 𝓤 ⁺ ⊔ 𝓥  ̇
Downward-Closed-Subsetₚ P = Downward-Closed-Subset (λ x y → x ≤[ P ] y)

\end{code}

\section{Downward closure}

\begin{code}

module Downward-Closure {A : 𝓤  ̇} (_⊑_ : A → A → Ω 𝓤) where

\end{code}

The downward closure of an element a.k.a. the principal ideal it generates.

\begin{code}

 ↓_ : A → 𝓟 A
 ↓ a = λ a′ → a′ ⊑ a

 infix 30 ↓_

\end{code}

The downward closure is downward closed.

\begin{code}

 ↓-is-downward-closed : is-transitive _⊑_ holds
                      → (a : A)
                      → is-downward-closed _⊑_ (↓ a) holds
 ↓-is-downward-closed τ a a₁ p a₂ q = τ a₂ a₁ a q p

\end{code}

The downward closure of a subset.

\begin{code}

 ↓ₛ_ : 𝓟 A → 𝓟 A
 ↓ₛ_ U = ⋃ {I = 𝕋 U} λ { (u , _) → ↓ u }
  where
   open unions-of-small-families pt 𝓤 𝓤 A

 infix 30 ↓ₛ_

\end{code}

The downward closure of a subset is downward closed.

\begin{code}

 ↓ₛ-is-downward-closed : is-transitive _⊑_ holds → (U : 𝓟 A) → is-downward-closed _⊑_ (↓ₛ U) holds
 ↓ₛ-is-downward-closed τ U a r a′ q = ∥∥-functor † r
  where
   † : Σ (u , _) ꞉ 𝕋 U , (a ⊑ u) holds → Σ (u , _) ꞉ 𝕋 U , (a′ ⊑ u) holds
   † ((u , p) , q′) = (u , p) , τ a′ a u q q′

\end{code}

\section{Intersection of downward closures}

\begin{code}

module Downward-Closure-Intersection-Syntax {A : 𝓤 ̇} (_⊑_ : A → A → Ω 𝓤) where

 open Downward-Closure _⊑_

 _⊓_ : 𝓟 A → 𝓟 A → 𝓟 A
 U ⊓ V = ↓ₛ U ∩ ↓ₛ V

 downward-closedness-implies-⊓-coincides-with-∩
  : propext 𝓤
  → is-reflexive _⊑_ holds
  → {U V : 𝓟 A}
  → is-downward-closed _⊑_ U holds
  → is-downward-closed _⊑_ V holds
  → U ⊓ V ＝ U ∩ V
 downward-closedness-implies-⊓-coincides-with-∩ pe 𝓇𝒻𝓁 {U} {V} φ ψ =
  subset-extensionality pe fe † ‡
   where
    † : (U ⊓ V) ⊆ (U ∩ V)
    † a (μ , ν) = ∥∥-rec₂ (holds-is-prop (a ∈ₚ (U ∩ V))) γ μ ν
     where
      γ : Σ (u , _) ꞉ 𝕋 U , (a ⊑ u) holds
        → Σ (v , _) ꞉ 𝕋 V , (a ⊑ v) holds
        → a ∈ₚ (U ∩ V) holds
      γ ((u , pu) , ru) ((v , pv) , rv)= φ u pu a ru , ψ v pv a rv

    ‡ : (U ∩ V) ⊆ (U ⊓ V)
    ‡ a (μ , ν) = ∣ (a , μ) , 𝓇𝒻𝓁 a ∣ , ∣ (a , ν) , 𝓇𝒻𝓁 a ∣

 infix 35 _⊓_

\end{code}
