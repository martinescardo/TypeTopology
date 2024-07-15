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


open import Locales.Compactness pt fe
open import Locales.DiscreteLocale.Definition fe pe pt
open import Locales.DiscreteLocale.Two fe pe pt
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.Frame pt fe hiding (∅)
open import Locales.Sierpinski 𝓤 pe pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import Locales.Stone pt fe sr
open import MLTT.List hiding ([_])
open import MLTT.Plus-Properties
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

\begin{code}

true-join-false-is-𝟏 : trueₖ ∨[ 𝒪 𝟚ₗ ] falseₖ ＝ 𝟏[ 𝒪 𝟚ₗ ]
true-join-false-is-𝟏 =
 only-𝟏-is-above-𝟏 (𝒪 𝟚ₗ) (trueₖ ∨[ 𝒪 𝟚ₗ ] falseₖ) †
  where
   † : (𝟏[ 𝒪 𝟚ₗ ] ≤[ poset-of (𝒪 𝟚ₗ) ] (trueₖ ∨[ 𝒪 𝟚ₗ ] falseₖ)) holds
   † ₀ ⋆ = ∣ inr ⋆ , refl ∣
   † ₁ ⋆ = ∣ inl ⋆ , refl ∣

false-join-true-is-𝟏 : falseₖ ∨[ 𝒪 𝟚ₗ ] trueₖ ＝ 𝟏[ 𝒪 𝟚ₗ ]
false-join-true-is-𝟏 =
 falseₖ ∨[ 𝒪 𝟚ₗ ] trueₖ   ＝⟨ Ⅰ ⟩
 trueₖ ∨[ 𝒪 𝟚ₗ ] falseₖ   ＝⟨ Ⅱ ⟩
 𝟏[ 𝒪 𝟚ₗ ]                ∎
  where
   Ⅰ = ∨[ 𝒪 𝟚ₗ ]-is-commutative falseₖ trueₖ
   Ⅱ = true-join-false-is-𝟏

\end{code}

These are the only compact opens of the locale `𝟚`. Accordingly, we can
construct the following intensional basis for it.

\begin{code}

Four : 𝓤  ̇
Four = 𝟚 𝓤 × 𝟚 𝓤

𝛃 : Four → ⟨ 𝒪 𝟚ₗ ⟩
𝛃 (₀ , ₀) = 𝟎[ 𝒪 𝟚ₗ ]
𝛃 (₀ , ₁) = falseₖ
𝛃 (₁ , ₀) = trueₖ
𝛃 (₁ , ₁) = full

ℬ-𝟚 : Fam 𝓤 ⟨ 𝒪 𝟚ₗ ⟩
ℬ-𝟚 = Four , 𝛃

\end{code}

We now prove that this is a spectral basis.

\begin{code}

cover-𝟚 : (U : ⟨ 𝒪 𝟚ₗ ⟩) → Fam 𝓤 Four
cover-𝟚 U = (U ₀ holds + U ₁ holds) , h
 where
  h : U ₀ holds + U ₁ holds → Four
  h (inl p) = (₀ , ₁)
  h (inr q) = (₁ , ₀)

ℬ-𝟚-is-basis : is-basis-for (𝒪 𝟚ₗ) ℬ-𝟚
ℬ-𝟚-is-basis U = cover-𝟚 U , †
 where
  open Joins (λ x y → x ≤[ poset-of (𝒪 𝟚ₗ) ] y)

  ψ : ((u′ , _) : upper-bound ⁅ ℬ-𝟚 [ i ] ∣ i ε (cover-𝟚 U) ⁆)
    → (U ≤[ poset-of (𝒪 𝟚ₗ) ] u′) holds
  ψ (u′ , φ) ₀ μ = φ (inl μ) ₀ refl
  ψ (u′ , φ) ₁ μ = φ (inr μ) ₁ refl

  υ : (U is-an-upper-bound-of ⁅ ℬ-𝟚 [ i ] ∣ i ε cover-𝟚 U ⁆) holds
  υ (inl p) ₀ _ = p
  υ (inr q) ₁ _ = q

  † : (U is-lub-of ⁅ ℬ-𝟚 [ i ] ∣ i ε cover-𝟚 U ⁆) holds
  † = υ , ψ

ℬ-𝟚↑ : Fam 𝓤 ⟨ 𝒪 (𝟚-loc 𝓤) ⟩
ℬ-𝟚↑ = directify (𝒪 𝟚ₗ) ℬ-𝟚

ℬ-𝟚↑-is-basis : is-basis-for (𝒪 𝟚ₗ) ℬ-𝟚↑
ℬ-𝟚↑-is-basis = directified-basis-is-basis (𝒪 𝟚ₗ) ℬ-𝟚 ℬ-𝟚-is-basis

ℬ-𝟚↑-is-directed-basis : directed-basis-forᴰ (𝒪 𝟚ₗ) ℬ-𝟚↑
ℬ-𝟚↑-is-directed-basis U = pr₁ (ℬ-𝟚↑-is-basis U)
                         , pr₂ (ℬ-𝟚↑-is-basis U)
                         , covers-of-directified-basis-are-directed (𝒪 𝟚ₗ) ℬ-𝟚 ℬ-𝟚-is-basis U

ℬ-𝟚-directed-basisᴰ : directed-basisᴰ (𝒪 𝟚ₗ)
ℬ-𝟚-directed-basisᴰ = ℬ-𝟚↑ , ℬ-𝟚↑-is-directed-basis

\end{code}

\begin{code}

ℬ-𝟚↑-is-spectral : consists-of-compact-opens 𝟚ₗ ℬ-𝟚↑ holds
ℬ-𝟚↑-is-spectral []           = 𝟎-is-compact 𝟚ₗ
ℬ-𝟚↑-is-spectral (₀ , ₀ ∷ is) = compact-opens-are-closed-under-∨
                                 𝟚ₗ
                                 𝟎[ 𝒪 𝟚ₗ ]
                                 (ℬ-𝟚↑ [ is ])
                                 (𝟎-is-compact 𝟚ₗ)
                                 (ℬ-𝟚↑-is-spectral is)
ℬ-𝟚↑-is-spectral (₀ , ₁ ∷ is) = compact-opens-are-closed-under-∨
                                 𝟚ₗ
                                 falseₖ
                                 (ℬ-𝟚↑ [ is ])
                                 falseₖ-is-compact
                                 (ℬ-𝟚↑-is-spectral is)
ℬ-𝟚↑-is-spectral (₁ , ₀ ∷ is) = compact-opens-are-closed-under-∨
                                 𝟚ₗ
                                 trueₖ
                                 (ℬ-𝟚↑ [ is ])
                                 trueₖ-is-compact
                                 (ℬ-𝟚↑-is-spectral is)
ℬ-𝟚↑-is-spectral (₁ , ₁ ∷ is) = compact-opens-are-closed-under-∨ 𝟚ₗ fullₖ (ℬ-𝟚↑ [ is ]) fullₖ-is-compact (ℬ-𝟚↑-is-spectral is)

\end{code}

\begin{code}

equal-to-one-of-the-four-compact-opens : (U : ⟨ 𝒪 𝟚ₗ ⟩) → 𝓤 ⁺  ̇
equal-to-one-of-the-four-compact-opens U =
 (U ＝ 𝟎[ 𝒪 𝟚ₗ ]) + (U ＝ falseₖ) + (U ＝ trueₖ) + (U ＝ 𝟏[ 𝒪 𝟚ₗ ])

basis-tetrachotomy : (is : List Four)
                   → equal-to-one-of-the-four-compact-opens (ℬ-𝟚↑ [ is ])
basis-tetrachotomy []           = inl refl
basis-tetrachotomy (₀ , ₀ ∷ is) =
 transport equal-to-one-of-the-four-compact-opens († ⁻¹) IH
  where
   † : ℬ-𝟚↑ [ (₀ , ₀) ∷ is ] ＝ ℬ-𝟚↑ [ is ]
   † = 𝟎-right-unit-of-∨ (𝒪 𝟚ₗ) (ℬ-𝟚↑ [ is ])

   IH : equal-to-one-of-the-four-compact-opens (ℬ-𝟚↑ [ is ])
   IH = basis-tetrachotomy is
basis-tetrachotomy ((₀ , ₁) ∷ is) = cases₄ case₁ case₂ case₃ case₄ IH
 where
  case₁ : ℬ-𝟚↑ [ is ] ＝ 𝟎[ 𝒪 (𝟚-loc 𝓤) ]
        → equal-to-one-of-the-four-compact-opens (ℬ-𝟚↑ [ ₀ , ₁ ∷ is ])
  case₁ p = inr (inl †)
   where
    Ⅰ = ap (λ - → falseₖ ∨[ 𝒪 𝟚ₗ ] -) p
    Ⅱ = 𝟎-left-unit-of-∨ (𝒪 𝟚ₗ) falseₖ

    † : ℬ-𝟚↑ [ ₀ , ₁ ∷ is ] ＝ falseₖ
    † = falseₖ ∨[ 𝒪 𝟚ₗ ] ℬ-𝟚↑ [ is ]   ＝⟨ Ⅰ ⟩
        falseₖ ∨[ 𝒪 𝟚ₗ ] 𝟎[ 𝒪 𝟚ₗ ]     ＝⟨ Ⅱ ⟩
        falseₖ                         ∎

  case₂ : ℬ-𝟚↑ [ is ] ＝ falseₖ
        → equal-to-one-of-the-four-compact-opens (ℬ-𝟚↑ [ ₀ , ₁ ∷ is ])
  case₂ p = inr (inl †)
   where
    Ⅰ = ap (λ - → falseₖ ∨[ 𝒪 𝟚ₗ ] -) p
    Ⅱ = ∨[ 𝒪 𝟚ₗ ]-is-idempotent falseₖ ⁻¹

    † : ℬ-𝟚↑ [ (₀ , ₁) ∷ is ] ＝ falseₖ
    † = falseₖ ∨[ 𝒪 𝟚ₗ ] ℬ-𝟚↑ [ is ]  ＝⟨ Ⅰ ⟩
        falseₖ ∨[ 𝒪 𝟚ₗ ] falseₖ       ＝⟨ Ⅱ ⟩
        falseₖ                        ∎

  case₃ : ℬ-𝟚↑ [ is ] ＝ trueₖ
        → equal-to-one-of-the-four-compact-opens (ℬ-𝟚↑ [ (₀ , ₁) ∷ is ])
  case₃ p = inr (inr (inr †))
   where
    † : ℬ-𝟚↑ [ (₀ , ₁) ∷ is ] ＝ 𝟏[ 𝒪 𝟚ₗ ]
    † = falseₖ ∨[ 𝒪 𝟚ₗ ] ℬ-𝟚↑ [ is ]    ＝⟨ Ⅰ ⟩
        falseₖ ∨[ 𝒪 𝟚ₗ ] trueₖ          ＝⟨ Ⅱ ⟩
        𝟏[ 𝒪 𝟚ₗ ]                       ∎
         where
          Ⅰ = ap (λ - → falseₖ ∨[ 𝒪 𝟚ₗ ] -) p
          Ⅱ = false-join-true-is-𝟏

  case₄ : ℬ-𝟚↑ [ is ] ＝ 𝟏[ 𝒪 (𝟚-loc 𝓤) ]
        → equal-to-one-of-the-four-compact-opens (ℬ-𝟚↑ [ (₀ , ₁) ∷ is ])
  case₄ p = inr (inr (inr †))
   where
    † : ℬ-𝟚↑ [ (₀ , ₁) ∷ is ] ＝ 𝟏[ 𝒪 (𝟚-loc 𝓤) ]
    † = ℬ-𝟚↑ [ (₀ , ₁) ∷ is ]                ＝⟨ Ⅰ ⟩
        ℬ-𝟚 [ (₀ , ₁) ] ∨[ 𝒪 𝟚ₗ ] 𝟏[ 𝒪 𝟚ₗ ]  ＝⟨ Ⅱ ⟩
        𝟏[ 𝒪 𝟚ₗ ]                            ∎
         where
          Ⅰ = ap (λ - → _ ∨[ 𝒪 𝟚ₗ ] -) p
          Ⅱ = 𝟏-right-annihilator-for-∨ (𝒪 𝟚ₗ) (ℬ-𝟚 [ (₀ , ₁) ])

  IH : equal-to-one-of-the-four-compact-opens (ℬ-𝟚↑ [ is ])
  IH = basis-tetrachotomy is
basis-tetrachotomy ((₁ , ₀) ∷ is) = cases₄ case₁ case₂ case₃ case₄ IH
 where
  case₁ : ℬ-𝟚↑ [ is ] ＝ 𝟎[ 𝒪 𝟚ₗ ]
        → equal-to-one-of-the-four-compact-opens (ℬ-𝟚↑ [ ₁ , ₀ ∷ is ])
  case₁ p = inr (inr (inl †))
   where
    Ⅰ = ap (λ - → trueₖ ∨[ 𝒪 𝟚ₗ ] -) p
    Ⅱ = 𝟎-left-unit-of-∨ (𝒪 𝟚ₗ) trueₖ

    † : ℬ-𝟚↑ [ (₁ , ₀) ∷ is ] ＝ trueₖ
    † = trueₖ ∨[ 𝒪 𝟚ₗ ] ℬ-𝟚↑ [ is ]   ＝⟨ Ⅰ ⟩
        trueₖ ∨[ 𝒪 𝟚ₗ ] 𝟎[ 𝒪 𝟚ₗ ]     ＝⟨ Ⅱ ⟩
        trueₖ                         ∎

  case₂ : ℬ-𝟚↑ [ is ] ＝ falseₖ
        → equal-to-one-of-the-four-compact-opens (ℬ-𝟚↑ [ ₁ , ₀ ∷ is ])
  case₂ p = inr (inr (inr †))
   where
    Ⅰ = ap (λ - → trueₖ ∨[ 𝒪 𝟚ₗ ] -) p
    Ⅱ = true-join-false-is-𝟏

    † : ℬ-𝟚↑ [ (₁ , ₀) ∷ is ] ＝ 𝟏[ 𝒪 𝟚ₗ ]
    † = trueₖ ∨[ 𝒪 𝟚ₗ ] ℬ-𝟚↑ [ is ]  ＝⟨ Ⅰ ⟩
        trueₖ ∨[ 𝒪 𝟚ₗ ] falseₖ       ＝⟨ Ⅱ ⟩
        𝟏[ 𝒪 𝟚ₗ ]                    ∎

  case₃ : ℬ-𝟚↑ [ is ] ＝ trueₖ
        → equal-to-one-of-the-four-compact-opens (ℬ-𝟚↑ [ ₁ , ₀ ∷ is ])
  case₃ p = inr (inr (inl †))
   where
    Ⅰ = ap (λ - → trueₖ ∨[ 𝒪 𝟚ₗ ] -) p
    Ⅱ = ∨[ 𝒪 𝟚ₗ ]-is-idempotent trueₖ ⁻¹

    † : ℬ-𝟚↑ [ (₁ , ₀) ∷ is ] ＝ trueₖ
    † = trueₖ ∨[ 𝒪 𝟚ₗ ] ℬ-𝟚↑ [ is ]   ＝⟨ Ⅰ ⟩
        trueₖ ∨[ 𝒪 𝟚ₗ ] trueₖ         ＝⟨ Ⅱ ⟩
        trueₖ                         ∎

  case₄ : ℬ-𝟚↑ [ is ] ＝ 𝟏[ 𝒪 𝟚ₗ ]
        → equal-to-one-of-the-four-compact-opens (ℬ-𝟚↑ [ ₁ , ₀ ∷ is ])
  case₄ p = inr (inr (inr †))
   where
    † : ℬ-𝟚↑ [ (₁ , ₀) ∷ is ] ＝ 𝟏[ 𝒪 𝟚ₗ ]
    † = ℬ-𝟚↑ [ (₁ , ₀) ∷ is ]                ＝⟨ Ⅰ ⟩
        ℬ-𝟚 [ (₁ , ₀) ] ∨[ 𝒪 𝟚ₗ ] 𝟏[ 𝒪 𝟚ₗ ]  ＝⟨ Ⅱ ⟩
        𝟏[ 𝒪 𝟚ₗ ]                            ∎
         where
          Ⅰ = ap (λ - → _ ∨[ 𝒪 𝟚ₗ ] -) p
          Ⅱ = 𝟏-right-annihilator-for-∨ (𝒪 𝟚ₗ) (ℬ-𝟚 [ (₁ , ₀) ])

  IH = basis-tetrachotomy is
basis-tetrachotomy ((₁ , ₁) ∷ is) =
 transport
  equal-to-one-of-the-four-compact-opens
  († ⁻¹)
  (inr (inr (inr refl)))
  where
   Ⅰ = 𝟏-left-annihilator-for-∨ (𝒪 𝟚ₗ) (ℬ-𝟚↑ [ is ])

   † : ℬ-𝟚↑ [ (₁ , ₁) ∷ is ] ＝ 𝟏[ 𝒪 𝟚ₗ ]
   † = 𝟏[ 𝒪 𝟚ₗ ] ∨[ 𝒪 𝟚ₗ ] ℬ-𝟚↑ [ is ] ＝⟨ Ⅰ ⟩ 𝟏[ 𝒪 𝟚ₗ ] ∎

\end{code}

Tetrachotomy for compact opens.

\begin{code}

compact-tetrachotomy : (U : ⟨ 𝒪 𝟚ₗ ⟩)
                     → is-compact-open 𝟚ₗ U holds
                     → ∥ equal-to-one-of-the-four-compact-opens U ∥
compact-tetrachotomy U κ = ∥∥-functor † γ
 where
  † : Σ is ꞉ List Four , (ℬ-𝟚↑ [ is ] ＝ U)
    → equal-to-one-of-the-four-compact-opens U
  † (is , p) = transport equal-to-one-of-the-four-compact-opens p ‡
   where
    ‡ : equal-to-one-of-the-four-compact-opens (ℬ-𝟚↑ [ is ])
    ‡ = basis-tetrachotomy is

  γ : is-basic (𝟚-loc 𝓤) U ℬ-𝟚-directed-basisᴰ holds
  γ = compact-opens-are-basic 𝟚ₗ ℬ-𝟚-directed-basisᴰ U κ

\end{code}

Added on 2024-07-15.

\begin{code}

ℬ-𝟚↑-contains-top : contains-top (𝒪 (𝟚-loc 𝓤)) ℬ-𝟚↑ holds
ℬ-𝟚↑-contains-top = ∣ ((₁ , ₁) ∷ []) , † ∣
 where
  p : 𝟏[ 𝒪 𝟚ₗ ] ＝ 𝟏[ 𝒪 𝟚ₗ ] ∨[ 𝒪 𝟚ₗ ] 𝟎[ 𝒪 𝟚ₗ ]
  p = 𝟏-left-annihilator-for-∨ (𝒪 𝟚ₗ) 𝟎[ 𝒪 𝟚ₗ ] ⁻¹

  † : is-top (𝒪 (𝟚-loc 𝓤)) (𝟏[ 𝒪 𝟚ₗ ] ∨[ 𝒪 𝟚ₗ ] 𝟎[ 𝒪 𝟚ₗ ]) holds
  † = transport (λ - → is-top (𝒪 (𝟚-loc 𝓤)) - holds) p (𝟏-is-top (𝒪 𝟚ₗ))

ℬ-𝟚↑-contains-bottom : contains-bottom (𝒪 (𝟚-loc 𝓤)) ℬ-𝟚↑ holds
ℬ-𝟚↑-contains-bottom = ∣ (((₀ , ₀) ∷ [])) , † ∣
 where
  p : 𝟎[ 𝒪 𝟚ₗ ] ＝ 𝟎[ 𝒪 𝟚ₗ ] ∨[ 𝒪 𝟚ₗ ] 𝟎[ 𝒪 𝟚ₗ ]
  p = ∨[ 𝒪 𝟚ₗ ]-is-idempotent 𝟎[ 𝒪 𝟚ₗ ]

  † : is-bottom (𝒪 (𝟚-loc 𝓤)) (𝟎[ 𝒪 𝟚ₗ ] ∨[ 𝒪 𝟚ₗ ] 𝟎[ 𝒪 𝟚ₗ ]) holds
  † = transport
       (λ - → is-bottom (𝒪 (𝟚-loc 𝓤)) - holds)
       p
       (𝟎-is-bottom (𝒪 𝟚ₗ))

\end{code}

Added on 2024-07-15.

\begin{code}

false-is-not-𝟎 : ¬ (𝟎[ 𝒪 (𝟚-loc 𝓤) ] ＝ falseₖ)
false-is-not-𝟎 p = ∥∥-rec 𝟘-is-prop (λ { (() , _) }) μ
 where
  μ : ₀ ∈ 𝟎[ 𝒪 (𝟚-loc 𝓤) ]
  μ = transport (λ - → ₀ ∈ -) (p ⁻¹) refl

false-is-not-𝟏 : ¬ (falseₖ ＝ 𝟏[ 𝒪 (𝟚-loc 𝓤) ])
false-is-not-𝟏 p = +disjoint (μ ⁻¹)
 where
  μ : ₁ ∈ falseₖ
  μ = transport (λ - → ₁ ∈ -) (p ⁻¹) ⋆

true-is-not-𝟎 : ¬ (trueₖ ＝ 𝟎[ 𝒪 (𝟚-loc 𝓤) ])
true-is-not-𝟎 p = ∥∥-rec 𝟘-is-prop (λ { (() , _) }) μ
 where
  μ : ₁ ∈ 𝟎[ 𝒪 (𝟚-loc 𝓤) ]
  μ = transport (λ - → ₁ ∈ -) p refl

true-is-not-𝟏 : ¬ (trueₖ ＝ 𝟏[ 𝒪 (𝟚-loc 𝓤) ])
true-is-not-𝟏 p = +disjoint μ
 where
  μ : ₀ ∈ trueₖ
  μ = transport (λ - → ₀ ∈ -) (p ⁻¹) ⋆

𝟎-is-not-𝟏 : ¬ (𝟎[ 𝒪 (𝟚-loc 𝓤) ] ＝ 𝟏[ 𝒪 (𝟚-loc 𝓤) ])
𝟎-is-not-𝟏 p = ∥∥-rec 𝟘-is-prop (λ { (() , _) }) μ
 where
  μ : ₁ ∈ 𝟎[ 𝒪 (𝟚-loc 𝓤) ]
  μ = transport (λ - → ₁ ∈ -) (p ⁻¹) ⋆

true-is-not-false : ¬ (trueₖ ＝ falseₖ)
true-is-not-false p = +disjoint (μ ⁻¹)
 where
  μ : ₁ ∈ falseₖ
  μ = transport (λ - → ₁ ∈ -) p refl

\end{code}

\begin{code}

being-equal-to-one-of-the-four-compact-opens-is-prop
 : (U : ⟨ 𝒪 𝟚ₗ ⟩)
 → is-prop (equal-to-one-of-the-four-compact-opens U)
being-equal-to-one-of-the-four-compact-opens-is-prop U (inl p) (inl q) =
 ap inl (carrier-of-[ poset-of (𝒪 𝟚ₗ) ]-is-set p q)
being-equal-to-one-of-the-four-compact-opens-is-prop U (inl p) (inr (inl q)) =
 𝟘-elim (false-is-not-𝟎 †)
  where
   † : 𝟎[ 𝒪 𝟚ₗ ] ＝ falseₖ
   † = 𝟎[ 𝒪 𝟚ₗ ] ＝⟨ p ⁻¹ ⟩ U ＝⟨ q ⟩ falseₖ ∎
being-equal-to-one-of-the-four-compact-opens-is-prop U (inl p) (inr (inr (inl q))) =
 𝟘-elim (true-is-not-𝟎 †)
  where
   † : trueₖ ＝ 𝟎[ 𝒪 (𝟚-loc 𝓤) ]
   † = trueₖ ＝⟨ q ⁻¹ ⟩ U ＝⟨ p ⟩ 𝟎[ 𝒪 (𝟚-loc 𝓤) ] ∎
being-equal-to-one-of-the-four-compact-opens-is-prop U (inl p) (inr (inr (inr q))) =
 𝟘-elim (𝟎-is-not-𝟏 †)
  where
   † : 𝟎[ 𝒪 (𝟚-loc 𝓤) ] ＝ 𝟏[ 𝒪 (𝟚-loc 𝓤) ]
   † = 𝟎[ 𝒪 (𝟚-loc 𝓤) ] ＝⟨ p ⁻¹ ⟩ U ＝⟨ q ⟩ 𝟏[ 𝒪 (𝟚-loc 𝓤) ] ∎
being-equal-to-one-of-the-four-compact-opens-is-prop U (inr (inl p)) (inl q) =
 𝟘-elim (false-is-not-𝟎 †)
  where
   † : 𝟎[ 𝒪 (𝟚-loc 𝓤) ] ＝ falseₖ
   † = 𝟎[ 𝒪 (𝟚-loc 𝓤) ] ＝⟨ q ⁻¹ ⟩ U ＝⟨ p ⟩ falseₖ ∎
being-equal-to-one-of-the-four-compact-opens-is-prop U (inr (inr (inl p))) (inl q) =
 𝟘-elim (true-is-not-𝟎 †)
  where
   † : trueₖ ＝ 𝟎[ 𝒪 (𝟚-loc 𝓤) ]
   † = trueₖ ＝⟨ p ⁻¹ ⟩ U ＝⟨ q ⟩ 𝟎[ 𝒪 (𝟚-loc 𝓤) ] ∎
being-equal-to-one-of-the-four-compact-opens-is-prop U (inr (inr (inr p))) (inl q) =
 𝟘-elim (𝟎-is-not-𝟏 †)
  where
   † :  𝟎[ 𝒪 (𝟚-loc 𝓤) ] ＝ 𝟏[ 𝒪 (𝟚-loc 𝓤) ]
   † =  𝟎[ 𝒪 (𝟚-loc 𝓤) ] ＝⟨ q ⁻¹ ⟩ U ＝⟨ p ⟩ 𝟏[ 𝒪 (𝟚-loc 𝓤) ] ∎
being-equal-to-one-of-the-four-compact-opens-is-prop U (inr (inl p)) (inr (inl q)) =
 ap (inr ∘ inl) (carrier-of-[ poset-of (𝒪 𝟚ₗ) ]-is-set p q)
being-equal-to-one-of-the-four-compact-opens-is-prop U (inr (inl p)) (inr (inr (inl q))) =
 𝟘-elim (true-is-not-false †)
  where
   † : trueₖ ＝ falseₖ
   † = trueₖ ＝⟨ q ⁻¹ ⟩ U ＝⟨ p ⟩ falseₖ ∎
being-equal-to-one-of-the-four-compact-opens-is-prop U (inr (inl p)) (inr (inr (inr q))) =
 𝟘-elim (false-is-not-𝟏 †)
  where
   † : falseₖ ＝ 𝟏[ 𝒪 (𝟚-loc 𝓤) ]
   † = falseₖ ＝⟨ p ⁻¹ ⟩ U ＝⟨ q ⟩ 𝟏[ 𝒪 (𝟚-loc 𝓤) ] ∎
being-equal-to-one-of-the-four-compact-opens-is-prop U (inr (inr (inl p))) (inr (inl q)) =
 𝟘-elim (true-is-not-false †)
  where
   † : trueₖ ＝ falseₖ
   † = trueₖ ＝⟨ p ⁻¹ ⟩ U ＝⟨ q ⟩ falseₖ ∎
being-equal-to-one-of-the-four-compact-opens-is-prop U (inr (inr (inr p))) (inr (inl q)) =
 𝟘-elim (false-is-not-𝟏 †)
  where
   † : falseₖ ＝ 𝟏[ 𝒪 (𝟚-loc 𝓤) ]
   † = falseₖ ＝⟨ q ⁻¹ ⟩ U ＝⟨ p ⟩ 𝟏[ 𝒪 (𝟚-loc 𝓤) ] ∎
being-equal-to-one-of-the-four-compact-opens-is-prop U (inr (inr (inl p))) (inr (inr (inl q))) =
 ap (inr ∘ inr ∘ inl) (carrier-of-[ poset-of (𝒪 𝟚ₗ) ]-is-set p q)
being-equal-to-one-of-the-four-compact-opens-is-prop U (inr (inr (inl p))) (inr (inr (inr q))) =
 𝟘-elim (true-is-not-𝟏 †)
  where
   † : trueₖ ＝ 𝟏[ 𝒪 (𝟚-loc 𝓤) ]
   † = trueₖ ＝⟨ p ⁻¹ ⟩ U ＝⟨ q ⟩ 𝟏[ 𝒪 (𝟚-loc 𝓤) ] ∎
being-equal-to-one-of-the-four-compact-opens-is-prop U (inr (inr (inr p))) (inr (inr (inl q))) =
 𝟘-elim (true-is-not-𝟏 †)
  where
   † : trueₖ ＝ 𝟏[ 𝒪 (𝟚-loc 𝓤) ]
   † = trueₖ ＝⟨ q ⁻¹ ⟩ U ＝⟨ p ⟩ 𝟏[ 𝒪 (𝟚-loc 𝓤) ] ∎
being-equal-to-one-of-the-four-compact-opens-is-prop U (inr (inr (inr p))) (inr (inr (inr q))) =
 ap (inr ∘ inr ∘ inr) (carrier-of-[ poset-of (𝒪 𝟚ₗ) ]-is-set p q)

\end{code}
