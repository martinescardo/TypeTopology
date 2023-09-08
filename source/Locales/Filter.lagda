Ayberk Tosun, 8 September 2023

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.FunExt
open import UF.EquivalenceExamples
open import MLTT.List hiding ([_])
open import MLTT.Pi
open import Slice.Family
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Logic

module Locales.Filter (pt : propositional-truncations-exist)
                      (fe : Fun-Ext)                            where

open import Locales.Frame pt fe
open import Locales.Compactness pt fe
open import UF.Powerset
open import UF.SubtypeClassifier

open Locale
open Universal fe
open Implication fe

\end{code}

\begin{code}

is-upwards-closed : (X : Locale 𝓤 𝓥 𝓦) → 𝓟 ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓥)
is-upwards-closed X S =
 Ɐ U ꞉ ⟨ 𝒪 X ⟩ , Ɐ V ꞉ ⟨ 𝒪 X ⟩ , (U ≤[ poset-of (𝒪 X) ] V) ⇒ S U ⇒ S V

\end{code}

\begin{code}

is-filter : (X : Locale 𝓤 𝓥 𝓦) → 𝓟 ⟨ 𝒪 X ⟩ → Ω {!!}
is-filter X F = {!!}

\end{code}
