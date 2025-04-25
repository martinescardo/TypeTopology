---
title: Some properties of nuclei and their fixed points
author: Ayberk Tosun
date-started: 2025-04-25
---

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module Locales.NucleusImage
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.Frame pt fe
open import Locales.Nucleus pt fe
open import UF.Equiv
open import UF.ImageAndSurjection pt
open import UF.Logic
open import UF.Subsingletons
open import UF.SubtypeClassifier

open AllCombinators pt fe
open FrameHomomorphismProperties
open FrameHomomorphisms
open Locale
open PropositionalTruncation pt

\end{code}

The set of fixed points of a nucleus coincides is equivalent to its image. This
is a standard fact of locale theory. See, for example, [Joh82, p. 49].

\begin{code}

fixed-points-of-nucleus-are-its-image : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
                                      → (j : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
                                      → is-nucleus (𝒪 X) j holds
                                      → image j ≃ (Σ U ꞉ ⟨ 𝒪 X ⟩ , j U ＝ U)
fixed-points-of-nucleus-are-its-image X j 𝓃 =
 s , (qinvs-are-equivs s (r , r-cancels-s , s-cancels-r))
  where
   s : image j → (Σ U ꞉ ⟨ 𝒪 X ⟩ , j U ＝ U)
   s (U , p) = U , ∥∥-rec carrier-of-[ poset-of (𝒪 X) ]-is-set † p
    where
     † : (Σ V ꞉ ⟨ 𝒪 X ⟩ , j V ＝ U) → j U ＝ U
     † (V , q) = j U      ＝⟨ Ⅰ ⟩
                 j (j V)  ＝⟨ Ⅱ ⟩
                 j V      ＝⟨ q ⟩
                 U        ∎
      where
       Ⅰ = ap j (q ⁻¹)
       Ⅱ = nuclei-are-idempotent (𝒪 X) (j , 𝓃) V

   r : (Σ U ꞉ ⟨ 𝒪 X ⟩ , j U ＝ U) → image j
   r (U , p) = U , ∣ U , p ∣

   s-cancels-r : s ∘ r ∼ id
   s-cancels-r (U , p) =
    to-subtype-＝ (λ _ → carrier-of-[ poset-of (𝒪 X) ]-is-set) refl

   r-cancels-s : r ∘ s ∼ id
   r-cancels-s (U , p) =
    to-subtype-＝ (λ - → being-in-the-image-is-prop - j) refl

\end{code}

[Joh82]: Peter T. Johstone. Stone Spaces. Cambridge Studies in Advanced
         Mathematics. Cambridge, 1982. ISBN: 978-0-521-33779-3
