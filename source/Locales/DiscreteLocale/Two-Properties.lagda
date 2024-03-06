--------------------------------------------------------------------------------
title:          Properties of the locale two
author:         Ayberk Tosun
date-started:   2024-03-04
--------------------------------------------------------------------------------

We define the locale corresponding to the two-point discrete space.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons

module Locales.DiscreteLocale.Two-Properties
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
        (𝓤  : Universe)
       where


open import Locales.DiscreteLocale.Definition fe pe pt
open import Locales.DiscreteLocale.Two fe pe pt
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.Frame pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import Locales.Sierpinski 𝓤 pe pt fe
open import Locales.Stone pt fe sr
-- open import Locales.PatchProperties pt fe sr
open import Locales.Compactness pt fe
open import Slice.Family
open import UF.DiscreteAndSeparated hiding (𝟚-is-set)
open import UF.Logic
open import UF.Powerset
open import UF.Sets
open import UF.SubtypeClassifier

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)
open Locale
open PropositionalSubsetInclusionNotation fe
open PropositionalTruncation pt hiding (_∨_)

\end{code}

Shorthand notation.

\begin{code}

𝟚ₗ : Locale (𝓤 ⁺) 𝓤 𝓤
𝟚ₗ = 𝟚-loc 𝓤

\end{code}

The locale two is compact.

\begin{code}

𝟚ₗ-is-compact : is-compact 𝟚ₗ holds
𝟚ₗ-is-compact S δ p = ∥∥-rec₂ ∃-is-prop † (p ₀ ⋆) (p ₁ ⋆)
 where
  open PosetNotation (poset-of (𝒪 𝟚ₗ))

  † : Σ i ꞉ index S , ₀ ∈ (S [ i ])
    → Σ j ꞉ index S , ₁ ∈ (S [ j ])
    → ∃ k ꞉ index S , full ⊆ (S [ k ])
  † (i , μᵢ) (j , μⱼ) = ∥∥-rec ∃-is-prop γ (pr₂ δ i j)
   where
    γ : Σ k ꞉ index S , ((S [ i ]) ⊆ₚ (S [ k ]) ∧ₚ (S [ j ]) ⊆ₚ (S [ k ])) holds
      → ∃ k ꞉ index S ,  full ⊆ (S [ k ])
    γ (k , φ , ψ) = ∣ k , β ∣
     where
      β : full ⊆ (S [ k ])
      β ₀ ⋆ = φ ₀ μᵢ
      β ₁ ⋆ = ψ ₁ μⱼ

\end{code}
