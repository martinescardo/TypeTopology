Ayberk Tosun, 11 September 2023

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.FunExt
open import UF.UA-FunExt

module Locales.Complements (pt : propositional-truncations-exist)
                           (fe : Fun-Ext)                           where

open import Locales.AdjointFunctorTheoremForFrames
open import Locales.Frame pt fe
open import Locales.WayBelow pt fe
open import Locales.Compactness pt fe
open import Slice.Family
open import UF.Logic
open import UF.SubtypeClassifier

open AllCombinators pt fe
open PropositionalTruncation pt

open import Locales.GaloisConnection pt fe

open import Locales.InitialFrame pt fe

open Locale

\end{code}

An open `x` in a frame `L` is *clopen* iff it has complement `x′`.

\begin{code}

is-boolean-complement-of : (L : Frame 𝓤 𝓥 𝓦) → ⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓤
is-boolean-complement-of F x′ x =
 (x ∧[ F ] x′ ＝[ iss ]＝ 𝟎[ F ]) ∧ (x ∨[ F ] x′ ＝[ iss ]＝ 𝟏[ F ])
  where
   iss = carrier-of-[ poset-of F ]-is-set

\end{code}

\begin{code}

complementation-is-symmetric : (F : Frame 𝓤 𝓥 𝓦) (x y : ⟨ F ⟩)
                             → (is-boolean-complement-of F x y
                             ⇒  is-boolean-complement-of F y x) holds
complementation-is-symmetric F x y (φ , ψ) = † , ‡
 where
  † : x ∧[ F ] y ＝ 𝟎[ F ]
  † = x ∧[ F ] y ＝⟨ ∧[ F ]-is-commutative x y ⟩ y ∧[ F ] x ＝⟨ φ ⟩ 𝟎[ F ] ∎

  ‡ : x ∨[ F ] y ＝ 𝟏[ F ]
  ‡ = x ∨[ F ] y ＝⟨ ∨[ F ]-is-commutative x y ⟩ y ∨[ F ] x ＝⟨ ψ ⟩ 𝟏[ F ] ∎

\end{code}
