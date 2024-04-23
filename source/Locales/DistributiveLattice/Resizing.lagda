---
title:          Transporting a distributive lattice along an equivalence
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

module Locales.DistributiveLattice.Resizing
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

 _∨₀_ : A → A → A
 _∨₀_ = λ x y → s (r x ∨ r y)

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
  s (r x ∧ r (s (r y ∧ r z)))  ＝⟨ Ⅰ    ⟩
  s (r x ∧ (r y ∧ r z))        ＝⟨ Ⅱ    ⟩
  s ((r x ∧ r y) ∧ r z)        ＝⟨ Ⅲ    ⟩
  s (r (s (r x ∧ r y)) ∧ r z)  ＝⟨ refl ⟩
  s (r (s (r x ∧ r y)) ∧ r z)  ＝⟨ refl ⟩
  (x ∧₀ y) ∧₀ z                ∎
   where
    Ⅰ = ap (λ - → s (r x ∧ -)) (r-cancels-s (r y ∧ r z))
    Ⅱ = ap s (∧-associative (r x) (r y) (r z))
    Ⅲ = ap (λ - → s (- ∧ r z)) (r-cancels-s (r x ∧ r y) ⁻¹)

 ∧₀-is-commutative : (x y : A) → x ∧₀ y ＝ y ∧₀ x
 ∧₀-is-commutative x y = ap s (∧-commutative (r x) (r y))

 ∧₀-unit : (x : A) → x ∧₀ s 𝟏L ＝ x
 ∧₀-unit x =
  s (r x ∧ r (s 𝟏L)) ＝⟨ Ⅰ ⟩
  s (r x ∧ 𝟏L)       ＝⟨ Ⅱ ⟩
  s (r x)            ＝⟨ Ⅲ ⟩
  x                  ∎
   where
    Ⅰ = ap (λ - → s (r x ∧ -)) (r-cancels-s 𝟏L)
    Ⅱ = ap s (∧-unit (r x))
    Ⅲ = s-cancels-r x

 ∧₀-idempotent : (x : A) → x ∧₀ x ＝ x
 ∧₀-idempotent x =
  s (r x ∧ r x) ＝⟨ Ⅰ ⟩
  s (r x)       ＝⟨ Ⅱ ⟩
  x             ∎
   where
    Ⅰ = ap s (∧-idempotent (r x))
    Ⅱ = s-cancels-r x

 ∧₀-absorptive : (x y : A) → x ∧₀ (x ∨₀ y) ＝ x
 ∧₀-absorptive x y =
  s (r x ∧ r (s (r x ∨ r y)))   ＝⟨ Ⅰ ⟩
  s (r x ∧ (r x ∨ r y))         ＝⟨ Ⅱ ⟩
  s (r x)                       ＝⟨ Ⅲ ⟩
  x                             ∎
   where
    Ⅰ = ap (λ - → s (r x ∧ -)) (r-cancels-s (r x ∨ r y))
    Ⅱ = ap s (∧-absorptive (r x) (r y))
    Ⅲ = s-cancels-r x

 ∨₀-associative : (x y z : A) → x ∨₀ (y ∨₀ z) ＝ (x ∨₀ y) ∨₀ z
 ∨₀-associative x y z =
  x ∨₀ (y ∨₀ z)                ＝⟨ refl ⟩
  s (r x ∨ r (s (r y ∨ r z)))  ＝⟨ Ⅰ    ⟩
  s (r x ∨ (r y ∨ r z))        ＝⟨ Ⅱ    ⟩
  s ((r x ∨ r y) ∨ r z)        ＝⟨ Ⅲ    ⟩
  s (r (s (r x ∨ r y)) ∨ r z)  ＝⟨ refl ⟩
  s (r (s (r x ∨ r y)) ∨ r z)  ＝⟨ refl ⟩
  (x ∨₀ y) ∨₀ z                ∎
   where
    Ⅰ = ap (λ - → s (r x ∨ -)) (r-cancels-s (r y ∨ r z))
    Ⅱ = ap s (∨-associative (r x) (r y) (r z))
    Ⅲ = ap (λ - → s (- ∨ r z)) (r-cancels-s (r x ∨ r y) ⁻¹)

 ∨₀-commutative : (x y : A) → x ∨₀ y ＝ y ∨₀ x
 ∨₀-commutative x y = ap s (∨-commutative (r x) (r y))

 ∨₀-unit : (x : A) → x ∨₀ s 𝟎L ＝ x
 ∨₀-unit x = s (r x ∨ r (s 𝟎L)) ＝⟨ Ⅰ ⟩
             s (r x ∨ 𝟎L)       ＝⟨ Ⅱ ⟩
             s (r x)            ＝⟨ Ⅲ ⟩
             x                  ∎
              where
               Ⅰ = ap (λ - → s (r x ∨ -)) (r-cancels-s 𝟎L)
               Ⅱ = ap s (∨-unit (r x))
               Ⅲ = s-cancels-r x

 ∨₀-idempotent : (x : A) → x ∨₀ x ＝ x
 ∨₀-idempotent x =
   s (r x ∨ r x) ＝⟨ Ⅰ ⟩
   s (r x)       ＝⟨ Ⅱ ⟩
   x             ∎
    where
     Ⅰ = ap s (∨-idempotent (r x))
     Ⅱ = s-cancels-r x

 ∨₀-absorptive : (x y : A) → x ∨₀ (x ∧₀ y) ＝ x
 ∨₀-absorptive x y =
  x ∨₀ (x ∧₀ y)                 ＝⟨ refl ⟩
  s (r x ∨ r (s (r x ∧ r y)))   ＝⟨ Ⅰ    ⟩
  s (r x ∨ (r x ∧ r y))         ＝⟨ Ⅱ    ⟩
  s (r x)                       ＝⟨ Ⅲ    ⟩
  x                             ∎
   where
    Ⅰ = ap (λ - → s (r x ∨ -)) (r-cancels-s (r x ∧ r y))
    Ⅱ = ap s (∨-absorptive (r x) (r y))
    Ⅲ = s-cancels-r x

 distributivity₀ᵈ : (x y z : A) → x ∧₀ (y ∨₀ z) ＝ (x ∧₀ y) ∨₀ (x ∧₀ z)
 distributivity₀ᵈ x y z =
  x ∧₀ (y ∨₀ z)                             ＝⟨ refl ⟩
  s (r x ∧ r (s (r y ∨ r z)))               ＝⟨ Ⅰ    ⟩
  s (r x ∧ (r y ∨ r z))                     ＝⟨ Ⅱ    ⟩
  s ((r x ∧ r y) ∨ (r x ∧ r z))             ＝⟨ Ⅲ    ⟩
  s ((r x ∧ r y) ∨ r (s (r x ∧ r z)))       ＝⟨ Ⅳ    ⟩
  s (r (s (r x ∧ r y)) ∨ r (s (r x ∧ r z))) ＝⟨ refl ⟩
  s (r (x ∧₀ y) ∨ r (x ∧₀ z))               ＝⟨ refl ⟩
  (x ∧₀ y) ∨₀ (x ∧₀ z)                      ∎
   where
    Ⅰ = ap (λ - → s (r x ∧ -)) (r-cancels-s (r y ∨ r z))
    Ⅱ = ap s (distributivityᵈ (r x) (r y) (r z))
    Ⅲ = ap (λ - → s ((r x ∧ r y) ∨ -)) (r-cancels-s (r x ∧ r z) ⁻¹)
    Ⅳ = ap (λ - → s (- ∨ r (s (r x ∧ r z)))) (r-cancels-s (r x ∧ r y) ⁻¹)

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
        ; ∧-commutative   = ∧₀-is-commutative
        ; ∧-unit          = ∧₀-unit
        ; ∧-idempotent    = ∧₀-idempotent
        ; ∧-absorptive    = ∧₀-absorptive
        ; ∨-associative   = ∨₀-associative
        ; ∨-commutative   = ∨₀-commutative
        ; ∨-unit          = ∨₀-unit
        ; ∨-idempotent    = ∨₀-idempotent
        ; ∨-absorptive    = ∨₀-absorptive
        ; distributivityᵈ = distributivity₀ᵈ
        }

\end{code}
