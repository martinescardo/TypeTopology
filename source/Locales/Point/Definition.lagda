Ayberk Tosun.

Started on 8  September 2023.
Updated on 21 September 2023.

This module contains the definition of point of a locale.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.EquivalenceExamples
open import UF.SubtypeClassifier
open import UF.Logic

module Locales.Point.Definition (pt : propositional-truncations-exist)
                                (fe : Fun-Ext)
                                where

open import UF.Powerset
open import Slice.Family
open import Locales.Frame  pt fe

open Locale

open AllCombinators pt fe

\end{code}

\begin{code}

module DefnOfCPF (X : Locale 𝓤 𝓥 𝓦) where

 open PosetNotation (poset-of (𝒪 X))

 closed-under-binary-meets : 𝓟 ⟨ 𝒪 X ⟩ → Ω 𝓤
 closed-under-binary-meets F =
  Ɐ U ꞉ ⟨ 𝒪 X ⟩ , Ɐ V ꞉ ⟨ 𝒪 X ⟩ , U ∈ₚ F ⇒ V ∈ₚ F ⇒ (U ∧[ 𝒪 X ] V) ∈ₚ F

 closed-under-finite-meets : 𝓟 ⟨ 𝒪 X ⟩ → Ω 𝓤
 closed-under-finite-meets F = 𝟏[ 𝒪 X ] ∈ₚ F ∧ closed-under-binary-meets F

 is-upwards-closed : 𝓟 ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓥)
 is-upwards-closed F = Ɐ U ꞉ ⟨ 𝒪 X ⟩ , Ɐ V ꞉ ⟨ 𝒪 X ⟩ , U ∈ₚ F ⇒ U ≤ V ⇒ V ∈ₚ F

 is-filter : 𝓟 ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓥)
 is-filter F = is-upwards-closed F ∧ closed-under-finite-meets F

 is-completely-prime : 𝓟 ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓦 ⁺)
 is-completely-prime F = Ɐ S ꞉ Fam 𝓦 ⟨ 𝒪 X ⟩ ,
                          (⋁[ 𝒪 X ] S) ∈ₚ F ⇒ (Ǝ i ꞉ index S , (S [ i ]) ∈ F)

 Point : 𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
 Point = Σ F ꞉ 𝓟 ⟨ 𝒪 X ⟩ , (is-filter F ∧ is-completely-prime F) holds

\end{code}
