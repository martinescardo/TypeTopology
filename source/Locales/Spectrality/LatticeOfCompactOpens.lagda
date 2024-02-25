---
title:        Distributive lattice of compact opens
author:       Ayberk Tosun
date-started: 2024-02-24
---

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.FunExt
open import UF.EquivalenceExamples
open import MLTT.List hiding ([_])
open import MLTT.Pi
open import Slice.Family
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.Subsingletons-FunExt
open import UF.Logic
open import UF.ImageAndSurjection
open import UF.Size

module Locales.Spectrality.LatticeOfCompactOpens
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
       where

open import Locales.Frame                          pt fe
open import Locales.Compactness                    pt fe
open import Locales.Spectrality.SpectralLocale     pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.SmallBasis pt fe sr

open PropositionalTruncation pt

open AllCombinators pt fe

open Locale

\end{code}

\begin{code}

module _ (X : Locale (𝓤 ⁺) 𝓤 𝓤)
         (σ : is-spectral X holds)
         -- is-spectral-with-small-basis
         where

 𝒦₀-X : 𝓤  ̇
 𝒦₀-X = {!!}

 𝟏-is-compact : is-compact-open X 𝟏[ 𝒪 X ] holds
 𝟏-is-compact = spectral-locales-are-compact X σ

 𝒦⦅X⦆⁺ : DistributiveLattice (𝓤 ⁺)
 𝒦⦅X⦆⁺ = record
          { X = 𝒦 X
          ; 𝟏 = 𝟏[ 𝒪 X ] , 𝟏-is-compact
          ; 𝟎 = 𝟎[ 𝒪 X ] , 𝟎-is-compact X
          ; _∧_ = _∧ₖ_
          ; _∨_ = _∨ₖ_
          ; X-is-set      = 𝒦-is-set X
          ; ∧-associative = λ (K₁ , κ₁) K₂ (K₃ , κ₃) → 𝒦-equality X {!!} {!!} {!!}
          ; ∧-commutative = {!!}
          ; ∧-unit = λ (K , κ) → 𝒦-equality X (binary-coherence X σ K 𝟏[ 𝒪 X ] κ 𝟏-is-compact) κ (𝟏-right-unit-of-∧ (𝒪 X) K)
          ; ∧-idempotent = {!!}
          ; ∧-absorptive = {!!}
          ; ∨-associative = {!!}
          ; ∨-commutative = {!!}
          ; ∨-unit = λ (K , κ) → 𝒦-equality X {K ∨[ 𝒪 X ] 𝟎[ 𝒪 X ]} {K} (compact-opens-are-closed-under-∨ X K 𝟎[ 𝒪 X ] κ (𝟎-is-compact X)) κ (𝟎-left-unit-of-∨ (𝒪 X) K)
          ; ∨-idempotent = λ (K , κ) → 𝒦-equality X {K ∨[ 𝒪 X ] K} {K} (compact-opens-are-closed-under-∨ X K K κ κ) κ (∨[ 𝒪 X ]-is-idempotent K ⁻¹)
          ; ∨-absorptive = {!!}
          ; distributivityᵈ = {!!}
          }
           where
            open OperationsOnCompactOpens X σ

\end{code}
