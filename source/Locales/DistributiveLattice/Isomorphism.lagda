--------------------------------------------------------------------------------
title:        Isomorphisms of distributive lattices
author:       Ayberk Tosun
date-started: 2024-04-24
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets

module Locales.DistributiveLattice.Isomorphism
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Homomorphism fe pt
open import Locales.Frame pt fe
open import MLTT.Spartan
open import UF.Base
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.SubtypeClassifier

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_)

\end{code}

We work in a module parameterized by a 𝓤-distributive-lattice `L₁` and a
𝓥-distributive-lattice `L₂`.

\begin{code}

module DistributiveLatticeIsomorphisms (L₁ : DistributiveLattice 𝓤)
                                       (L₂ : DistributiveLattice 𝓥) where

\end{code}

The type `Isomorphismᵈᵣ L₁ L₂`, defined below, is the type of isomorphisms
between distributive lattices `L₁` and `L₂`.

\begin{code}

 record Isomorphismᵈᵣ : (𝓤 ⊔ 𝓥) ⁺  ̇ where
  field
   𝓈 : L₁ ─d→ L₂
   𝓇 : L₂ ─d→ L₁

  s : ∣ L₁ ∣ᵈ → ∣ L₂ ∣ᵈ
  s = Homomorphismᵈᵣ.h 𝓈

  r : ∣ L₂ ∣ᵈ → ∣ L₁ ∣ᵈ
  r = Homomorphismᵈᵣ.h 𝓇

  s-is-homomorphism : is-homomorphismᵈ L₁ L₂ s holds
  s-is-homomorphism = Homomorphismᵈᵣ.h-is-homomorphism 𝓈

  r-is-homomorphism : is-homomorphismᵈ L₂ L₁ r holds
  r-is-homomorphism = Homomorphismᵈᵣ.h-is-homomorphism 𝓇

\end{code}

Pretty syntax for `Isomorphismᵈᵣ`.

\begin{code}

Isomorphismᵈᵣ-Syntax : DistributiveLattice 𝓤
                     → DistributiveLattice 𝓥
                     → (𝓤 ⊔ 𝓥) ⁺  ̇
Isomorphismᵈᵣ-Syntax K L = DistributiveLatticeIsomorphisms.Isomorphismᵈᵣ K L

infix 0 Isomorphismᵈᵣ-Syntax
syntax Isomorphismᵈᵣ-Syntax K L = K ≅f≅ L

\end{code}
