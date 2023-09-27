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

We define the standard notion of _completely prime filter_.

\begin{code}

module DefnOfCPF (X : Locale (𝓤 ⁺) 𝓤 𝓤) where

 open PosetNotation (poset-of (𝒪 X))

 closed-under-binary-meets : (⟨ 𝒪 X ⟩ → Ω 𝓤) → Ω (𝓤 ⁺)
 closed-under-binary-meets F =
  Ɐ U ꞉ ⟨ 𝒪 X ⟩ , Ɐ V ꞉ ⟨ 𝒪 X ⟩ , U ∈ₚ F ⇒ V ∈ₚ F ⇒ (U ∧[ 𝒪 X ] V) ∈ₚ F

 closed-under-finite-meets : (⟨ 𝒪 X ⟩ → Ω 𝓤) → Ω (𝓤 ⁺)
 closed-under-finite-meets F = 𝟏[ 𝒪 X ] ∈ₚ F ∧ closed-under-binary-meets F

 is-upwards-closed : (⟨ 𝒪 X ⟩ → Ω 𝓤) → Ω (𝓤 ⁺)
 is-upwards-closed ϕ = Ɐ U ꞉ ⟨ 𝒪 X ⟩ , Ɐ V ꞉ ⟨ 𝒪 X ⟩ , (ϕ U) ⇒ U ≤ V ⇒ ϕ V

 is-filter : (⟨ 𝒪 X ⟩ → Ω 𝓤) → Ω (𝓤 ⁺)
 is-filter ϕ = is-upwards-closed ϕ ∧ closed-under-finite-meets ϕ

 is-completely-prime : (⟨ 𝒪 X ⟩ → Ω 𝓤) → Ω (𝓤 ⁺)
 is-completely-prime ϕ = Ɐ S ꞉ Fam 𝓤 ⟨ 𝒪 X ⟩ ,
                          ϕ (⋁[ 𝒪 X ] S) ⇒ (Ǝ i ꞉ index S , ϕ (S [ i ]) holds)

\end{code}

The type of points of a locale is then the completely prime filters.

\begin{code}

 Point : 𝓤 ⁺  ̇
 Point = Σ ϕ ꞉ (⟨ 𝒪 X ⟩ → Ω 𝓤) , (is-filter ϕ ∧ is-completely-prime ϕ) holds

\end{code}

With this definition of point as a completely prime filter, the points of a
locale `X` must be in bijection with continuous maps `𝟏 → X` (where `Ω` denotes
the terminal locale).

TODO: prove this fact.
