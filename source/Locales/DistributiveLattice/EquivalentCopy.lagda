---
title:          Equivalent copy of a distributive lattice
author:         Ayberk Tosun
date-started:   2024-04-22
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

module Locales.DistributiveLattice.EquivalentCopy
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

private
 fe : Fun-Ext
 fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

open import Locales.Compactness pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Homomorphism fe pt
open import Locales.Frame pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import UF.Equiv
open import UF.Sets
open import UF.Sets-Properties

open AllCombinators pt fe hiding (_∧_; _∨_)
open Locale
open PropositionalTruncation pt hiding (_∨_)

\end{code}

\begin{code}

module _ (L : DistributiveLattice 𝓤)
         (A : 𝓥  ̇)
         (e : ∣ L ∣ᵈ ≃ A) where

 open DistributiveLattice L renaming (𝟏 to 𝟏L; 𝟎 to 𝟎L)

 s : ∣ L ∣ᵈ → A
 s = ⌜ e ⌝

 r : A → ∣ L ∣ᵈ
 r = inverse ⌜ e ⌝ (⌜⌝-is-equiv e)

 r-cancels-s : r ∘ s ∼ id
 r-cancels-s = inverses-are-retractions s (⌜⌝-is-equiv e)

 s-cancels-r : s ∘ r ∼ id
 s-cancels-r x = pr₂ (pr₁ (pr₂ e)) x

 _∧₀_ : A → A → A
 _∧₀_ = λ x y → s (r x ∧ r y)

 r-preserves-∧ : (x y : A) → r (x ∧₀ y) ＝ r x ∧ r y
 r-preserves-∧ x y = r-cancels-s (r x ∧ r y)

 s-preserves-∧ : (x y : X) → s (x ∧ y) ＝ s x ∧₀ s y
 s-preserves-∧ x y = s (x ∧ y)             ＝⟨ Ⅰ ⟩
                     s (x ∧ r (s y))       ＝⟨ Ⅱ ⟩
                     s (r (s x) ∧ r (s y)) ∎
                      where
                       Ⅰ = ap (λ - → s (x ∧ -)) (r-cancels-s y) ⁻¹
                       Ⅱ = ap (λ - → s (- ∧ r (s y))) (r-cancels-s x ⁻¹)

 ∧₀-is-associative : (x y z : A) → x ∧₀ (y ∧₀ z) ＝ (x ∧₀ y) ∧₀ z
 ∧₀-is-associative x y z =
  x ∧₀ (y ∧₀ z)                ＝⟨ refl ⟩
  s (r x ∧ r (s (r y ∧ r z)))  ＝⟨ {!!} ⟩
  s (r (s (r x ∧ r y)) ∧ r z)  ＝⟨ refl ⟩
  s (r (s (r x ∧ r y)) ∧ r z)  ＝⟨ refl ⟩
  (x ∧₀ y) ∧₀ z                ∎

 L′₀ : DistributiveLattice 𝓥
 L′₀ = record
        { X               = A
        ; 𝟏               = s 𝟏L
        ; 𝟎               = s 𝟎L
        ; _∧_             = λ x y → s (r x ∧ r y)
        ; _∨_             = λ x y → s (r x ∨ r y)
        ; X-is-set        = equiv-to-set
                             (≃-sym e)
                             carrier-of-[ poset-ofᵈ L ]-is-set
        ; ∧-associative   = ∧₀-is-associative
        ; ∧-commutative   = {!!}
        ; ∧-unit          = {!!}
        ; ∧-idempotent    = {!!}
        ; ∧-absorptive    = {!!}
        ; ∨-associative   = {!!}
        ; ∨-commutative   = {!!}
        ; ∨-unit          = {!!}
        ; ∨-idempotent    = {!!}
        ; ∨-absorptive    = {!!}
        ; distributivityᵈ = {!!}
        }

\end{code}
