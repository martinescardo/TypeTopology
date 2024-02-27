---
title:          Distributive lattice of compact opens
author:         Ayberk Tosun
date-started:   2024-02-24
date-completed: 2024-02-27
---

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.List hiding ([_])
open import MLTT.Pi
open import MLTT.Spartan
open import Slice.Family
open import UF.Base
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.FunExt
open import UF.ImageAndSurjection
open import UF.Logic
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.UA-FunExt
open import UF.Univalence

module Locales.Spectrality.LatticeOfCompactOpens
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

fe : Fun-Ext
fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

open import Locales.Frame pt fe
open import Locales.Compactness pt fe
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.SmallBasis pt fe sr

open AllCombinators pt fe
open Locale
open PropositionalTruncation pt

\end{code}

We fix a large and locally small locale `X`, assumed to be spectral with a small
type of compact opens.

\begin{code}

module _ (X  : Locale (𝓤 ⁺) 𝓤 𝓤)
         (σ₀ : is-spectral-with-small-basis ua X holds) where

\end{code}

We define some shorthand notation to simplify the proofs.

\begin{code}

 σ : is-spectral X holds
 σ = ssb-implies-spectral ua X σ₀

 𝟏-is-compact : is-compact-open X 𝟏[ 𝒪 X ] holds
 𝟏-is-compact = spectral-locales-are-compact X σ

 𝟏ₖ : 𝒦 X
 𝟏ₖ = 𝟏[ 𝒪 X ] , 𝟏-is-compact

\end{code}

We now construct the distributive lattice of compact opens.

\begin{code}

 𝒦⦅X⦆ : DistributiveLattice (𝓤 ⁺)
 𝒦⦅X⦆ =
  record
   { X               = 𝒦 X
   ; 𝟏               = 𝟏ₖ
   ; 𝟎               = 𝟎[ 𝒪 X ] , 𝟎-is-compact X
   ; _∧_             = _∧ₖ_
   ; _∨_             = _∨ₖ_
   ; X-is-set        = 𝒦-is-set X
   ; ∧-associative   = α
   ; ∧-commutative   = β
   ; ∧-unit          = γ
   ; ∧-idempotent    = δ
   ; ∧-absorptive    = ϵ
   ; ∨-associative   = ζ
   ; ∨-commutative   = η
   ; ∨-unit          = θ
   ; ∨-idempotent    = ι
   ; ∨-absorptive    = μ
   ; distributivityᵈ = ν
   }
    where
     open OperationsOnCompactOpens X σ

\end{code}

The compact opens obviously satisfy all the distributive lattices, since every
frame is also a distributive lattice. Because the type `𝒦 X` of compact opens
packages up the opens of the frame together with their proofs of compactness
though, we need to lift these proofs from `𝒪 X` to `𝒦 X`. We take care of this
bureaucracy below.

\begin{code}

     α : (𝒦₁ 𝒦₂ 𝒦₃ : 𝒦 X) → 𝒦₁ ∧ₖ (𝒦₂ ∧ₖ 𝒦₃) ＝ (𝒦₁ ∧ₖ 𝒦₂) ∧ₖ 𝒦₃
     α 𝒦₁@(K₁ , κ₁) 𝒦₂@(K₂ , κ₂) 𝒦₃@(K₃ , κ₃) = 𝒦-equality X κ κ′ †
      where
       κ : is-compact-open X (K₁ ∧[ 𝒪 X ] (K₂ ∧[ 𝒪 X ] K₃)) holds
       κ = binary-coherence X σ _ _ κ₁ (binary-coherence X σ K₂ K₃ κ₂ κ₃)

       κ′ : is-compact-open X ((K₁ ∧[ 𝒪 X ] K₂) ∧[ 𝒪 X ] K₃) holds
       κ′ = binary-coherence X σ _ _ (binary-coherence X σ K₁ K₂ κ₁ κ₂) κ₃

       † : K₁ ∧[ 𝒪 X ] (K₂ ∧[ 𝒪 X ] K₃) ＝ (K₁ ∧[ 𝒪 X ] K₂) ∧[ 𝒪 X ] K₃
       † = ∧[ 𝒪 X ]-is-associative K₁ K₂ K₃

     β : (𝒦₁ 𝒦₂ : 𝒦 X) → 𝒦₁ ∧ₖ 𝒦₂ ＝ 𝒦₂ ∧ₖ 𝒦₁
     β (K₁ , κ₁) (K₂ , κ₂) = 𝒦-equality
                              X
                              (binary-coherence X σ K₁ K₂ κ₁ κ₂)
                              (binary-coherence X σ K₂ K₁ κ₂ κ₁)
                              (∧[ 𝒪 X ]-is-commutative K₁ K₂)

     γ : (𝒦 : 𝒦 X) → 𝒦 ∧ₖ 𝟏ₖ ＝ 𝒦
     γ (K , κ) = 𝒦-equality
                  X
                  (binary-coherence X σ K 𝟏[ 𝒪 X ] κ 𝟏-is-compact)
                  κ
                  (𝟏-right-unit-of-∧ (𝒪 X) K)

     δ : (𝒦 : 𝒦 X) → 𝒦 ∧ₖ 𝒦 ＝ 𝒦
     δ (K , κ) = 𝒦-equality
                  X
                  (binary-coherence X σ K K κ κ)
                  κ
                  (∧[ 𝒪 X ]-is-idempotent K ⁻¹ )

     ϵ : (𝒦₁ 𝒦₂ : 𝒦 X) → 𝒦₁ ∧ₖ (𝒦₁ ∨ₖ 𝒦₂) ＝ 𝒦₁
     ϵ (K₁ , κ₁) (K₂ , κ₂) = 𝒦-equality X κ κ₁ (absorptionᵒᵖ-right (𝒪 X) K₁ K₂)
      where
       κ : is-compact-open X (K₁ ∧[ 𝒪 X ] (K₁ ∨[ 𝒪 X ] K₂)) holds
       κ = binary-coherence
            X
            σ
            K₁
            (K₁ ∨[ 𝒪 X ] K₂)
            κ₁
            (compact-opens-are-closed-under-∨ X K₁ K₂ κ₁ κ₂)

     ζ : (𝒦₁ 𝒦₂ 𝒦₃ : 𝒦 X) → 𝒦₁ ∨ₖ (𝒦₂ ∨ₖ 𝒦₃) ＝ (𝒦₁ ∨ₖ 𝒦₂) ∨ₖ 𝒦₃
     ζ 𝒦₁@(K₁ , κ₁) 𝒦₂@(K₂ , κ₂) 𝒦₃@(K₃ , κ₃) =
      𝒦-equality
       X
       (compact-opens-are-closed-under-∨ X K₁ (K₂ ∨[ 𝒪 X ] K₃) κ₁ κ)
       (compact-opens-are-closed-under-∨ X (K₁ ∨[ 𝒪 X ] K₂) K₃ κ′ κ₃)
       (∨[ 𝒪 X ]-assoc K₁ K₂ K₃ ⁻¹)
        where
         κ : is-compact-open X (K₂ ∨[ 𝒪 X ] K₃) holds
         κ = compact-opens-are-closed-under-∨ X K₂ K₃ κ₂ κ₃

         κ′ : is-compact-open X (K₁ ∨[ 𝒪 X ] K₂) holds
         κ′ = compact-opens-are-closed-under-∨ X K₁ K₂ κ₁ κ₂

     η : (𝒦₁ 𝒦₂ : 𝒦 X) → 𝒦₁ ∨ₖ 𝒦₂ ＝ 𝒦₂ ∨ₖ 𝒦₁
     η 𝒦₁@(K₁ , κ₁) 𝒦₂@(K₂ , κ₂) =
      𝒦-equality
       X
       (compact-opens-are-closed-under-∨ X K₁ K₂ κ₁ κ₂)
       (compact-opens-are-closed-under-∨ X K₂ K₁ κ₂ κ₁)
       (∨[ 𝒪 X ]-is-commutative K₁ K₂)

     θ : (𝒦 : 𝒦 X) → 𝒦 ∨ₖ (𝟎[ 𝒪 X ] , 𝟎-is-compact X) ＝ 𝒦
     θ (K , κ) =
      𝒦-equality
       X
       (compact-opens-are-closed-under-∨ X K 𝟎[ 𝒪 X ] κ (𝟎-is-compact X))
       κ
       (𝟎-left-unit-of-∨ (𝒪 X) K)

     ι : (𝒦 : 𝒦 X) → 𝒦 ∨ₖ 𝒦 ＝ 𝒦
     ι (K , κ) = 𝒦-equality
                  X
                  (compact-opens-are-closed-under-∨ X K K κ κ)
                  κ
                  (∨[ 𝒪 X ]-is-idempotent K ⁻¹)

     μ : (𝒦₁ 𝒦₂ : 𝒦 X) → 𝒦₁ ∨ₖ (𝒦₁ ∧ₖ 𝒦₂) ＝ 𝒦₁
     μ 𝒦₁@(K₁ , κ₁) 𝒦₂@(K₂ , κ₂) =
      𝒦-equality
       X
       (compact-opens-are-closed-under-∨ X K₁ (K₁ ∧[ 𝒪 X ] K₂) κ₁ κ)
       κ₁
       (absorption-right (𝒪 X) K₁ K₂)
        where
         κ : is-compact-open X (K₁ ∧[ 𝒪 X ] K₂) holds
         κ = binary-coherence X σ K₁ K₂ κ₁ κ₂

     ν : (𝒦₁ 𝒦₂ 𝒦₃ : 𝒦 X) → 𝒦₁ ∧ₖ (𝒦₂ ∨ₖ 𝒦₃) ＝ (𝒦₁ ∧ₖ 𝒦₂) ∨ₖ (𝒦₁ ∧ₖ 𝒦₃)
     ν 𝒦₁@(K₁ , κ₁) 𝒦₂@(K₂ , κ₂) 𝒦₃@(K₃ , κ₃) = 𝒦-equality X κ κ′ †
       where
        κ  = binary-coherence
              X
              σ
              K₁
              (K₂ ∨[ 𝒪 X ] K₃)
              κ₁
              (compact-opens-are-closed-under-∨ X K₂ K₃ κ₂ κ₃)
        κ′ = compact-opens-are-closed-under-∨
              X
              (K₁ ∧[ 𝒪 X ] K₂)
              (K₁ ∧[ 𝒪 X ] K₃)
              (binary-coherence X σ K₁ K₂ κ₁ κ₂)
              (binary-coherence X σ K₁ K₃ κ₁ κ₃)

        † : K₁ ∧[ 𝒪 X ] (K₂ ∨[ 𝒪 X ] K₃) ＝ (K₁ ∧[ 𝒪 X ] K₂) ∨[ 𝒪 X ] (K₁ ∧[ 𝒪 X ] K₃)
        † = binary-distributivity (𝒪 X) K₁ K₂ K₃

\end{code}

The lattice `𝒦⦅X⦆` is a small distributive lattice.

\begin{code}

 𝒦⦅X⦆-is-small : is-small ∣ 𝒦⦅X⦆ ∣ᵈ
 𝒦⦅X⦆-is-small = smallness-of-𝒦 ua X σ₀

\end{code}
