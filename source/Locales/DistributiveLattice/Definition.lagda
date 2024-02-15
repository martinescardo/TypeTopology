---
title:       Distributive lattices
author:      Ayberk Tosun
start-date:  2024-02-14
---

\begin{code}

open import UF.PropTrunc
open import UF.FunExt

module Locales.DistributiveLattice.Definition
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.Frame pt fe
open import MLTT.Spartan
open import UF.Base
open import UF.SubtypeClassifier
open import UF.Logic

open Implication fe

\end{code}

\begin{code}

open import UF.Powerset-MultiUniverse

\end{code}

We first give the following record-based definition of distributive lattices.

\begin{code}

record DistributiveLatticeᵣ (𝓤 𝓥 : Universe) : 𝓤 ⁺ ⊔ 𝓥 ⁺  ̇ where
 field
  P   : Poset 𝓤 𝓥
  𝟏   : ∣ P ∣ₚ
  𝟎   : ∣ P ∣ₚ
  _∧_ : ∣ P ∣ₚ → ∣ P ∣ₚ → ∣ P ∣ₚ
  _∨_ : ∣ P ∣ₚ → ∣ P ∣ₚ → ∣ P ∣ₚ

 open Meets (λ x y → x ≤[ P ] y) renaming (is-top to is-top₀)
 open Joins (λ x y → x ≤[ P ] y)

 field
  𝟏-is-topᵈ       : is-top₀ 𝟏 holds
  𝟎-is-bottomᵈ    : is-least 𝟎 holds
  ∧-gives-glb     : (x y : ∣ P ∣ₚ) → ((x ∧ y) is-glb-of  (x , y)) holds
  ∨-gives-lub     : (x y : ∣ P ∣ₚ) → ((x ∨ y) is-lub-of₂ (x , y)) holds
  distributivityᵈ : (x y z : ∣ P ∣ₚ) → x ∧ (y ∨ z) ＝ (x ∧ y) ∨ (x ∧ z)

 ∧-lower-bound₁ : (x y : ∣ P ∣ₚ) → ((x ∧ y) ≤[ P ] x) holds
 ∧-lower-bound₁ x y = glb-is-an-upper-bound₁ (∧-gives-glb x y)

 ∧-lower-bound₂ : (x y : ∣ P ∣ₚ) → ((x ∧ y) ≤[ P ] y) holds
 ∧-lower-bound₂ x y = glb-is-an-upper-bound₂ (∧-gives-glb x y)

 ∧-greatest : {x y z : ∣ P ∣ₚ}
            → (z is-a-lower-bound-of (x , y) ⇒ z ≤[ P ] (x ∧ y)) holds
 ∧-greatest {x} {y} = glb-is-greatest (∧-gives-glb x y)

 ∨-upper-bound₁ : {x y : ∣ P ∣ₚ} → (x ≤[ P ] x ∨ y) holds
 ∨-upper-bound₁ {x} {y} = lub₂-is-an-upper-bound₁ (∨-gives-lub x y)

 ∨-upper-bound₂ : {x y : ∣ P ∣ₚ} → (y ≤[ P ] x ∨ y) holds
 ∨-upper-bound₂ {x} {y} = lub₂-is-an-upper-bound₂ (∨-gives-lub x y)

 ∨-least : {x y z : ∣ P ∣ₚ}
         → (z is-an-upper-bound-of₂ (x , y) ⇒ (x ∨ y) ≤[ P ] z) holds
 ∨-least {x} {y} = lub₂-is-least (∨-gives-lub x y)

\end{code}

\begin{code}

∣_∣ᵈ : DistributiveLatticeᵣ 𝓤 𝓥 → 𝓤  ̇
∣_∣ᵈ L = let open DistributiveLatticeᵣ L in ∣ P ∣ₚ

\end{code}
