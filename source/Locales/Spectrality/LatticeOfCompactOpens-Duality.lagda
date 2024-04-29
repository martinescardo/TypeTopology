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
open import UF.Base
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.FunExt
open import UF.ImageAndSurjection
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.UA-FunExt
open import UF.Univalence

module Locales.Spectrality.LatticeOfCompactOpens-Duality
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

private
 fe : Fun-Ext
 fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

 pe : Prop-Ext
 pe {𝓤} = univalence-gives-propext (ua 𝓤)

open import Locales.Compactness pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Homomorphism fe pt
open import Locales.DistributiveLattice.Ideal pt fe pe
open import Locales.DistributiveLattice.Isomorphism fe pt
open import Locales.DistributiveLattice.LocaleOfSpectra fe pe pt
open import Locales.DistributiveLattice.Resizing ua pt sr
open import Locales.Frame pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.LatticeOfCompactOpens ua pt sr
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import Slice.Family
open import UF.Classifiers
open import UF.Equiv hiding (_■)
open import UF.Logic
open import UF.Powerset-MultiUniverse hiding (𝕋)

open AllCombinators pt fe hiding (_∨_)
open Locale
open PropositionalTruncation pt hiding (_∨_)

\end{code}

We fix a large and locally small locale `X`, assumed to be spectral with a small
type of compact opens.

\begin{code}

module 𝒦-Duality (X  : Locale (𝓤 ⁺) 𝓤 𝓤)
                 (σ₀ : is-spectral-with-small-basis ua X holds) where

 open 𝒦-Lattice X σ₀

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

\begin{code}

 open DistributiveLatticeResizing 𝒦⦅X⦆ 𝒦⁻ (≃-sym (resizing-condition 𝒦⦅X⦆-is-small)) renaming (Lᶜ to 𝒦-X⁻)

 𝒦-isomorphism : 𝒦⦅X⦆ ≅d≅ 𝒦-X⁻
 𝒦-isomorphism = copy-isomorphic-to-original

\end{code}

\begin{code}

 open DefnOfFrameOfIdeal 𝒦-X⁻

\end{code}

\begin{code}

 spec-𝒦-X : Locale (𝓤 ⁺) 𝓤 𝓤
 spec-𝒦-X = locale-of-spectra

 ι : ∣ 𝒦-X⁻ ∣ᵈ → ⟨ 𝒪 X ⟩
 ι K = let (K′ , _) = r K in K′


 open Ideal
 open DistributiveLattice 𝒦-X⁻ using () renaming (𝟎 to 𝟎⁻; _∨_ to _∨⁻_)
 open DistributiveLattice 𝒦⦅X⦆ using (𝟎; _∨_)

 ι-preserves-𝟎 : ι 𝟎⁻ ＝ 𝟎[ 𝒪 X ]
 ι-preserves-𝟎 = ι 𝟎⁻ ＝⟨ refl ⟩ pr₁ (r (s 𝟎)) ＝⟨ ap pr₁ (r-cancels-s 𝟎) ⟩ 𝟎[ 𝒪 X ] ∎

 open PosetReasoning (poset-of (𝒪 X))
 open OperationsOnCompactOpens X σ

 ι-preserves-∨ : (K₁ K₂ : 𝒦⁻)
               → ι (K₁ ∨⁻ K₂) ＝ ι K₁ ∨[ 𝒪 X ] ι K₂
 ι-preserves-∨ K₁ K₂ =
  ιₖ (r (K₁ ∨⁻ K₂))                 ＝⟨ Ⅰ    ⟩
  ιₖ (r K₁ ∨ r K₂)                  ＝⟨ Ⅱ    ⟩
  pr₁ (r K₁) ∨[ 𝒪 X ] pr₁ (r K₂)    ＝⟨ refl ⟩
  ι K₁ ∨[ 𝒪 X ] ι K₂                ∎
   where
    Ⅰ = ap pr₁ (r-preserves-∨ K₁ K₂)
    Ⅱ = ιₖ-preserves-∨ (r K₁) (r K₂)

 ι-is-monotone : (K₁ K₂ : 𝒦⁻)
               → (K₁ ≤ᵈ[ 𝒦-X⁻ ] K₂ ⇒ ι K₁ ≤[ poset-of (𝒪 X) ] ι K₂) holds
 ι-is-monotone K₁ K₂ p = connecting-lemma₃ (𝒪 X) †
  where
   † : ι K₂ ＝ ι K₁ ∨[ 𝒪 X ] ι K₂
   † = ι K₂               ＝⟨ Ⅰ ⟩
       ι (K₁ ∨⁻ K₂)       ＝⟨ Ⅱ ⟩
       ι K₁ ∨[ 𝒪 X ] ι K₂ ∎
        where
         Ⅰ = ap ι (orderᵈ-implies-orderᵈ-∨ 𝒦-X⁻ p ⁻¹)
         Ⅱ = ι-preserves-∨ K₁ K₂

\end{code}

\begin{code}

 η : ⟨ 𝒪 X ⟩ → 𝓟 𝒦⁻
 η U = λ c → ι c ≤[ poset-of (𝒪 X) ] U

 η-contains-𝟎 : (U : ⟨ 𝒪 X ⟩) → 𝟎⁻ ∈ η U
 η-contains-𝟎 U = ι 𝟎⁻       ＝⟨ Ⅰ ⟩ₚ
                  𝟎[ 𝒪 X ]   ≤⟨ Ⅱ ⟩
                  U          ■
                   where
                    Ⅰ = ι-preserves-𝟎
                    Ⅱ = 𝟎-is-bottom (𝒪 X) U

\end{code}

\begin{code}

 η-is-downward-closed : (U : ⟨ 𝒪 X ⟩) → is-downward-closed 𝒦-X⁻ (η U) holds
 η-is-downward-closed U K₁ K₂ p μ =
  ιₖ (r K₁)   ≤⟨ Ⅰ ⟩
  ιₖ (r K₂)   ≤⟨ Ⅱ ⟩
  U           ■
   where
    Ⅰ = ι-is-monotone K₁ K₂ p
    Ⅱ = μ

\end{code}

\begin{code}

 η-is-closed-under-∨ : (U : ⟨ 𝒪 X ⟩)
                     → is-closed-under-binary-joins 𝒦-X⁻ (η U) holds
 η-is-closed-under-∨ U K₁ K₂ μ₁ μ₂  = †
  where
   foo : (ι K₁ ≤[ poset-of (𝒪 X) ] U) holds
   foo = μ₁

   baz : ((ι K₁ ∨[ 𝒪 X ] ι K₂) ≤[ poset-of (𝒪 X) ] U) holds
   baz = ∨[ 𝒪 X ]-least μ₁ μ₂

   † : (ι (K₁ ∨⁻ K₂) ≤[ poset-of (𝒪 X) ] U) holds
   † = ι (K₁ ∨⁻ K₂) ＝⟨ ι-preserves-∨ K₁ K₂ ⟩ₚ ι K₁ ∨[ 𝒪 X ] ι K₂ ≤⟨ baz ⟩ U ■

\end{code}

\begin{code}

 ϕ₀ : ⟨ 𝒪 X ⟩ → Ideal 𝒦-X⁻
 ϕ₀ U = record
         { I                    = η U
         ; I-is-inhabited       = ∣ 𝟎⁻ , η-contains-𝟎 U ∣
         ; I-is-downward-closed = η-is-downward-closed U
         ; I-is-closed-under-∨  = η-is-closed-under-∨ U
         }

\end{code}

\begin{code}

 open classifier-single-universe 𝓤

 open IdealNotation 𝒦-X⁻

 join : Ideal 𝒦-X⁻  → ⟨ 𝒪 X ⟩
 join ℐ = ⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ ℐ) ⁆

\end{code}
