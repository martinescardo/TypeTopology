---
title:          Properties of the locale two
author:         Ayberk Tosun
date-started:   2024-03-04
---

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
open import Locales.Frame pt fe hiding (∅)
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.Sierpinski 𝓤 pe pt fe
open import Locales.Stone pt fe sr
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

Added on 2024-06-22.

\begin{code}

fullₖ : ⟨ 𝒪 𝟚ₗ ⟩
fullₖ = full

fullₖ-is-compact : is-compact-open 𝟚ₗ fullₖ holds
fullₖ-is-compact = 𝟚ₗ-is-compact

𝟎-equal-to-∅ : ∅ ＝ 𝟎[ 𝒪 𝟚ₗ ]
𝟎-equal-to-∅ = only-𝟎-is-below-𝟎 (𝒪 𝟚ₗ) ∅ (λ _ → 𝟘-elim)

empty-is-compact : is-compact-open 𝟚ₗ ∅ holds
empty-is-compact =
 transport
  (λ - → is-compact-open 𝟚ₗ - holds)
  (𝟎-equal-to-∅ ⁻¹)
  (𝟎-is-compact 𝟚ₗ)

\end{code}

The singleton set `{ ₀ }`.

\begin{code}

falseₖ : ⟨ 𝒪 𝟚ₗ ⟩
falseₖ = λ x → x ＝ₚ ₀
 where
  open Equality (𝟚-is-set 𝓤)

\end{code}

\begin{code}

falseₖ-is-compact : is-compact-open 𝟚ₗ falseₖ holds
falseₖ-is-compact S δ p = ∥∥-functor † (p ₀ refl)
 where
  † : Σ k ꞉ index S , (S [ k ]) ₀ holds
    → Σ i ꞉ index S , (poset-of (𝒪 𝟚ₗ) PosetNotation.≤ falseₖ) (S [ i ]) holds
  † (k , μ) = k , (λ x q → transport (λ - → (S [ k ]) - holds) (q ⁻¹) μ)

\end{code}

We denote by `trueₖ` the singleton set `{ ₁ }`.

\begin{code}

trueₖ : ⟨ 𝒪 𝟚ₗ ⟩
trueₖ = λ x → x ＝ₚ ₁
 where
  open Equality (𝟚-is-set 𝓤)

\end{code}

The singleton `trueₖ` is compact.

\begin{code}

trueₖ-is-compact : is-compact-open 𝟚ₗ trueₖ holds
trueₖ-is-compact S δ p = ∥∥-functor † (p ₁ refl)
 where
  † : Σ k ꞉ index S , (S [ k ]) ₁ holds
    → Σ i ꞉ index S , (poset-of (𝒪 𝟚ₗ) PosetNotation.≤ trueₖ) (S [ i ]) holds
  † (k , μ) = k , (λ x q → transport (λ - → (S [ k ]) - holds) (q ⁻¹) μ)

\end{code}

These are the only compact opens of the locale `𝟚`. Accordingly, we can
construct the following intensional basis for it.

\begin{code}

Four : 𝓤  ̇
Four = 𝟚 𝓤 × 𝟚 𝓤

𝛃 : Four → ⟨ 𝒪 𝟚ₗ ⟩
𝛃 (₀ , ₀) = ∅
𝛃 (₀ , ₁) = falseₖ
𝛃 (₁ , ₀) = trueₖ
𝛃 (₁ , ₁) = full

ℬ-𝟚 : Fam 𝓤 ⟨ 𝒪 𝟚ₗ ⟩
ℬ-𝟚 = Four , 𝛃

\end{code}

We now prove that this is a spectral basis.

\begin{code}

cover-𝟚 : (U : ⟨ 𝒪 𝟚ₗ ⟩) → Fam 𝓤 Four
cover-𝟚 U = ((U ₀ holds + ¬ (U ₀ holds)) × (¬ (U ₁ holds) + U ₁ holds)) , h
 where
  h : (U ₀ holds + ¬ (U ₀ holds)) × (¬ (U ₁ holds) + U ₁ holds) → Four
  h (inl p , inl q) = ₀ , ₁
  h (inl p , inr q) = ₁ , ₁
  h (inr p , inl q) = ₀ , ₀
  h (inr p , inr q) = ₁ , ₀

ℬ-𝟚-is-basis : is-basis-for (𝒪 𝟚ₗ) ℬ-𝟚
ℬ-𝟚-is-basis U = cover-𝟚 U , †
 where
  open Joins (λ x y → x ≤[ poset-of (𝒪 𝟚ₗ) ] y)

  foo : ((u′ , _) : upper-bound ⁅ ℬ-𝟚 [ i ] ∣ i ε (cover-𝟚 U) ⁆)
      → (U ≤[ poset-of (𝒪 𝟚ₗ) ] u′) holds
  foo (u′ , φ) ₀ p = {!!}
  foo (u′ , φ) ₁ p = {!!}

  υ : (U is-an-upper-bound-of ⁅ ℬ-𝟚 [ i ] ∣ i ε (cover-𝟚 U) ⁆) holds
  υ = {!!}

  † : (U is-lub-of ⁅ ℬ-𝟚 [ i ] ∣ i ε cover-𝟚 U ⁆) holds
  † = υ , {!!}

ℬ-𝟚-is-directed-basis : is-directed-basis (𝒪 𝟚ₗ) ℬ-𝟚
ℬ-𝟚-is-directed-basis = ℬ-𝟚-is-basis , {!!}

\end{code}
