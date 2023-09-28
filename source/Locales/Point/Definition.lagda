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
open import UF.Equiv

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
 closed-under-finite-meets ϕ = 𝟏[ 𝒪 X ] ∈ₚ ϕ ∧ closed-under-binary-meets ϕ

 is-upwards-closed : (⟨ 𝒪 X ⟩ → Ω 𝓤) → Ω (𝓤 ⁺)
 is-upwards-closed ϕ = Ɐ U ꞉ ⟨ 𝒪 X ⟩ , Ɐ V ꞉ ⟨ 𝒪 X ⟩ , U ≤ V ⇒ ϕ U ⇒ ϕ V

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


We give an equivalent definition using records for the convenience of having
projections

\begin{code}

record Pointᵣ (X : Locale (𝓤 ⁺) 𝓤 𝓤) : 𝓤 ⁺  ̇ where
 open DefnOfCPF X

 field
  point : ⟨ 𝒪 X ⟩ → Ω 𝓤

  point-is-filter           : is-filter           point holds
  point-is-completely-prime : is-completely-prime point holds

 point-is-upwards-closed : is-upwards-closed point holds
 point-is-upwards-closed = pr₁ point-is-filter

 point-is-closed-under-finite-meets : closed-under-finite-meets point holds
 point-is-closed-under-finite-meets = pr₂ point-is-filter

 point-is-closed-under-∧ : closed-under-binary-meets point holds
 point-is-closed-under-∧ = pr₂ point-is-closed-under-finite-meets

 point-contains-top : (𝟏[ 𝒪 X ] ∈ₚ point) holds
 point-contains-top = pr₁ point-is-closed-under-finite-meets

open DefnOfCPF

to-pointᵣ : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Point X → Pointᵣ X
to-pointᵣ X x = record
                 { point                     = pr₁ x
                 ; point-is-filter           = pr₁ (pr₂ x)
                 ; point-is-completely-prime = pr₂ (pr₂ x)
                 }

to-point : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Pointᵣ X → Point X
to-point X x = point x , point-is-filter x , point-is-completely-prime x
 where
  open Pointᵣ

point-rec-equiv : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Pointᵣ X ≃ Point X
point-rec-equiv X =
 to-point X , (to-pointᵣ X , λ _ → refl) , (to-pointᵣ X) , (λ _ → refl)

\end{code}
