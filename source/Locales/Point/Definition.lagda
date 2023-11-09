Ayberk Tosun.

Started on 8  September 2023.
Updated on 21 September 2023.

This module contains the definition of point of a locale.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

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

open import UF.Powerset-MultiUniverse
open import Slice.Family
open import Locales.Frame  pt fe

open Locale

open AllCombinators pt fe

\end{code}

We define the standard notion of _completely prime filter_.

\begin{code}

module DefnOfCPF (X : Locale (𝓤 ⁺) 𝓤 𝓤) where

 open PosetNotation (poset-of (𝒪 X))

 closed-under-binary-meets : 𝓟 {𝓤} ⟨ 𝒪 X ⟩ → Ω (𝓤 ⁺)
 closed-under-binary-meets F =
  Ɐ U ꞉ ⟨ 𝒪 X ⟩ , Ɐ V ꞉ ⟨ 𝒪 X ⟩ , U ∈ₚ F ⇒ V ∈ₚ F ⇒ (U ∧[ 𝒪 X ] V) ∈ₚ F

 closed-under-finite-meets : 𝓟 ⟨ 𝒪 X ⟩ → Ω (𝓤 ⁺)
 closed-under-finite-meets ϕ = 𝟏[ 𝒪 X ] ∈ₚ ϕ ∧ closed-under-binary-meets ϕ

 is-upwards-closed : 𝓟 {𝓤} ⟨ 𝒪 X ⟩ → Ω (𝓤 ⁺)
 is-upwards-closed ϕ = Ɐ U ꞉ ⟨ 𝒪 X ⟩ , Ɐ V ꞉ ⟨ 𝒪 X ⟩ , U ≤ V ⇒ ϕ U ⇒ ϕ V

 is-filter : 𝓟 {𝓤} ⟨ 𝒪 X ⟩ → Ω (𝓤 ⁺)
 is-filter ϕ = is-upwards-closed ϕ ∧ closed-under-finite-meets ϕ

 is-completely-prime : 𝓟 {𝓤} ⟨ 𝒪 X ⟩ → Ω (𝓤 ⁺)
 is-completely-prime ϕ = Ɐ S ꞉ Fam 𝓤 ⟨ 𝒪 X ⟩ ,
                          ϕ (⋁[ 𝒪 X ] S) ⇒ (Ǝ i ꞉ index S , ϕ (S [ i ]) holds)

 is-cpf : 𝓟 ⟨ 𝒪 X ⟩ → Ω (𝓤 ⁺)
 is-cpf ϕ = is-filter ϕ ∧ is-completely-prime ϕ

\end{code}

The type of points of a locale is then the completely prime filters.

\begin{code}

 Point : 𝓤 ⁺  ̇
 Point = Σ ϕ ꞉ 𝓟 {𝓤} ⟨ 𝒪 X ⟩ , is-cpf ϕ holds

\end{code}

With this definition of point as a completely prime filter, the points of a
locale `X` must be in bijection with continuous maps `𝟏 → X` (where `𝟏` denotes
the terminal locale).

\section{Equivalent definitions using records}

We give two equivalent definitions using records to avoid using projections
and pairings to construct inhabitants of the `Point` type.

  * `Pointᵣ` corresponds directly to the Σ definition of `Point`.
  * `Point′ᵣ` is another equivalent definition that breaks down the conjuncts
    involved in the notion of being a completely prime filter. This is
    convenient when constructing inhabitants of `Point`.

\begin{code}

record Pointᵣ (X : Locale (𝓤 ⁺) 𝓤 𝓤) : 𝓤 ⁺  ̇ where
 open DefnOfCPF X

 field
  point        : 𝓟 ⟨ 𝒪 X ⟩
  point-is-cpf : is-cpf point holds

 point-is-filter : is-filter point holds
 point-is-filter = pr₁ point-is-cpf

 point-is-completely-prime : is-completely-prime point holds
 point-is-completely-prime = pr₂ point-is-cpf

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
to-pointᵣ X (ϕ , cpf) = record { point = ϕ ; point-is-cpf = cpf }

to-point : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Pointᵣ X → Point X
to-point X x = point x , point-is-filter x , point-is-completely-prime x
 where
  open Pointᵣ

point-rec-equiv : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Pointᵣ X ≃ Point X
point-rec-equiv X =
 to-point X , (to-pointᵣ X , λ _ → refl) , (to-pointᵣ X) , (λ _ → refl)

\end{code}

\begin{code}

record Point′ᵣ (X : Locale (𝓤 ⁺) 𝓤 𝓤) : 𝓤 ⁺  ̇ where
 field
  point                     : 𝓟 {𝓤} ⟨ 𝒪 X ⟩
  point-is-upwards-closed   : is-upwards-closed X point holds
  point-contains-top        : (𝟏[ 𝒪 X ] ∈ₚ point) holds
  point-is-closed-under-∧   : closed-under-binary-meets X point holds
  point-is-completely-prime : is-completely-prime X point holds

 point-is-cpf : is-cpf X point holds
 point-is-cpf = (⦅𝟏⦆ , ⦅𝟐⦆ , ⦅𝟑⦆) , ⦅𝟒⦆
  where
   ⦅𝟏⦆ : is-upwards-closed X point holds
   ⦅𝟏⦆ = point-is-upwards-closed

   ⦅𝟐⦆ : 𝟏[ 𝒪 X ] ∈ point
   ⦅𝟐⦆ = point-contains-top

   ⦅𝟑⦆ : closed-under-binary-meets X point holds
   ⦅𝟑⦆ = point-is-closed-under-∧

   ⦅𝟒⦆ : is-completely-prime X point holds
   ⦅𝟒⦆ = point-is-completely-prime

\end{code}

\begin{code}

to-point′ᵣ : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Pointᵣ X → Point′ᵣ X
to-point′ᵣ X 𝓍 =
 record
  { point                     = Pointᵣ.point 𝓍
  ; point-is-upwards-closed   = Pointᵣ.point-is-upwards-closed 𝓍
  ; point-contains-top        = Pointᵣ.point-contains-top 𝓍
  ; point-is-closed-under-∧   = Pointᵣ.point-is-closed-under-∧ 𝓍
  ; point-is-completely-prime = Pointᵣ.point-is-completely-prime 𝓍
  }

point′ᵣ-to-pointᵣ : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Point′ᵣ X → Pointᵣ X
point′ᵣ-to-pointᵣ X 𝓍 =
 record
  { point        = Point′ᵣ.point 𝓍
  ; point-is-cpf = Point′ᵣ.point-is-cpf 𝓍
  }

\end{code}
