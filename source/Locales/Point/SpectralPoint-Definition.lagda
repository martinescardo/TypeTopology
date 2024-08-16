---
title:          The notion of spectral point
author:         Ayberk Tosun
date-started:   2024-05-27
---

A _spectral point_ of a locale `X` is a continuous map `p : 𝟏 → X` whose right
adjoint `p^* : 𝒪(X) → 𝒪(𝟏)` preserves compact opens.

In this module, we give the definition of this notion. We define it using
records for the sake of convenience, and prove that the record-based definition
is equivalent to the standard definition.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.List hiding ([_])
open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

module Locales.Point.SpectralPoint-Definition
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Locales.Compactness pt fe
open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.Frame pt fe
open import Locales.InitialFrame pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import UF.Equiv
open import UF.SubtypeClassifier

open Locale

\end{code}

We work in a module parameterized by a large and locally small locale `X`.

\begin{code}

module Notion-Of-Spectral-Point (X : Locale (𝓤 ⁺) 𝓤 𝓤) where

 open ContinuousMaps X (𝟏Loc pe)
 open FrameHomomorphisms (𝒪 X) (𝟎-𝔽𝕣𝕞 pe)

\end{code}

A _spectral point_ of locale `X` is a frame homomorphism `𝒪(X) → Ω`
preserving compact opens. In other words, it is a spectral map `𝟏 → X`.

In the following definition, we call the underlying function of this frame
homomorphism `point-fn.

\begin{code}

 record Spectral-Point : 𝓤 ⁺  ̇ where
  field
   point-fn : ⟨ 𝒪 X ⟩ → Ω 𝓤

   point-preserves-top          : preserves-top point-fn holds
   point-preserves-binary-meets : preserves-binary-meets point-fn holds
   point-preserves-joins        : preserves-joins point-fn holds
   point-preserves-compactness  : (K : ⟨ 𝒪 X ⟩)
                                → is-compact-open X K holds
                                → is-compact-open (𝟏Loc pe) (point-fn K) holds

  point-is-a-frame-homomorphism : is-a-frame-homomorphism point-fn holds
  point-is-a-frame-homomorphism = point-preserves-top
                                , point-preserves-binary-meets
                                , point-preserves-joins

  point : _─f→_
  point = point-fn , point-is-a-frame-homomorphism

\end{code}

This record-based definition is of course just a more verbose way of writing
“spectral map into the initial frame”. We call this alternative definition
`Spectral-Point₀` and prove its equivalence to the type `Spectral-Point`.

\begin{code}

 Spectral-Point₀ : 𝓤 ⁺  ̇
 Spectral-Point₀ = Spectral-Map (𝟏Loc pe) X

 to-spectral-point₀ : Spectral-Point → Spectral-Point₀
 to-spectral-point₀ sp = (point-fn , †) , point-preserves-compactness
  where
   open Spectral-Point sp

   † : is-a-frame-homomorphism point-fn holds
   † = point-is-a-frame-homomorphism

 to-spectral-point : Spectral-Map (𝟏Loc pe) X → Spectral-Point
 to-spectral-point ((F , α , β , γ) , σ) =
  record
   { point-fn                     = F
   ; point-preserves-top          = α
   ; point-preserves-binary-meets = β
   ; point-preserves-joins        = γ
   ; point-preserves-compactness  = σ
   }

\end{code}

The equivalence proof.

\begin{code}

 spectral-point-equivalent-to-spectral-map-into-Ω
  : Spectral-Point₀ ≃ Spectral-Point
 spectral-point-equivalent-to-spectral-map-into-Ω =
  to-spectral-point , qinvs-are-equivs to-spectral-point †
   where
    † : qinv to-spectral-point
    † = to-spectral-point₀ , (λ _ → refl) , (λ _ → refl)

\end{code}

To show that two spectral points are equal, it suffices to show that their
underlying functions are equal. We call this lemma `to-spectral-point-＝`.

\begin{code}

 open Spectral-Point

 to-spectral-point-＝ : (ℱ 𝒢 : Spectral-Point)
                      → point-fn ℱ ＝ point-fn 𝒢
                      → ℱ ＝ 𝒢
 to-spectral-point-＝ ℱ 𝒢 p =
  ℱ                                          ＝⟨ Ⅰ ⟩
  to-spectral-point (to-spectral-point₀ ℱ)   ＝⟨ Ⅱ ⟩
  to-spectral-point (to-spectral-point₀ 𝒢)   ＝⟨ Ⅲ ⟩
  𝒢                                          ∎
  where
   e = spectral-point-equivalent-to-spectral-map-into-Ω

   † : to-spectral-point₀ ℱ ＝ to-spectral-point₀ 𝒢
   † = to-subtype-＝
        (holds-is-prop ∘ is-spectral-map X (𝟏Loc pe))
        (to-subtype-＝ (holds-is-prop ∘ is-a-frame-homomorphism) p)

   Ⅰ = inverses-are-sections' e ℱ
   Ⅱ = ap to-spectral-point †
   Ⅲ = inverses-are-sections' e 𝒢 ⁻¹

\end{code}

Added on 2024-08-12.

\begin{code}

 to-spectral-point-＝' : (ℱ 𝒢 : Spectral-Point) → point ℱ ＝ point 𝒢 → ℱ ＝ 𝒢
 to-spectral-point-＝' ℱ 𝒢 p =
  ℱ                                           ＝⟨ Ⅰ ⟩
  to-spectral-point (to-spectral-point₀ ℱ)    ＝⟨ Ⅱ ⟩
  to-spectral-point (to-spectral-point₀ 𝒢)    ＝⟨ Ⅲ ⟩
  𝒢                                           ∎
   where
    e = spectral-point-equivalent-to-spectral-map-into-Ω

    † : to-spectral-point₀ ℱ ＝ to-spectral-point₀ 𝒢
    † = to-subtype-＝ (holds-is-prop ∘ is-spectral-map X (𝟏Loc pe)) p

    Ⅰ = inverses-are-sections' e ℱ
    Ⅱ = ap to-spectral-point †
    Ⅲ = inverses-are-sections' e 𝒢 ⁻¹

\end{code}
