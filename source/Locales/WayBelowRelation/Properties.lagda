Ayberk Tosun, 19 August 2023

The module contains properties of the way below relation defined in
`Locales.WayBelowRelation.Definition`.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt
open import MLTT.Spartan
open import UF.Logic
open import UF.SubtypeClassifier
open import Slice.Family

module Locales.WayBelowRelation.Properties (pt : propositional-truncations-exist)
                                           (fe : Fun-Ext) where

open import Locales.WayBelowRelation.Definition pt fe

open import Locales.Frame pt fe

open PropositionalTruncation pt

open AllCombinators pt fe
open Locale

\end{code}

`𝟎` is way below anything.

\begin{code}

𝟎-is-way-below-anything : (X : Locale 𝓤 𝓥 𝓦)
                        → (U : ⟨ 𝒪 X ⟩) → (𝟎[ 𝒪 X ] ≪[ 𝒪 X ] U) holds
𝟎-is-way-below-anything X U S (ι , _) p = ∥∥-rec ∃-is-prop † ι
 where
  † : index S → ∃ i ꞉ index S , (𝟎[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] S [ i ]) holds
  † i = ∣ i , 𝟎-is-bottom (𝒪 X) (S [ i ]) ∣

\end{code}
