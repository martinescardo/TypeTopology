Alice Laroche, 27th September 2023

We show the identification of two alternative definition of 𝟚ᴹ,
and their equality under univalence.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Sets-Properties
open import UF.Univalence
open import UF.Universes

module Iterative.Multisets-IdentificationExample
        (ua : Univalence)
       where

open import Iterative.Multisets 𝓤₀
open import Iterative.Multisets-Addendum ua 𝓤₀
open import MLTT.Two
open import UF.Equiv
open import UF.EquivalenceExamples
open import W.Type

𝟚ᴹ : 𝕄
𝟚ᴹ = ssup 𝟚 (𝟚-cases 𝟘ᴹ 𝟙ᴹ)

𝟚ᴹ' : 𝕄
𝟚ᴹ' = ssup 𝟚 (𝟚-cases 𝟙ᴹ 𝟘ᴹ)

𝟚ᴹ≃ᴹ𝟚ᴹ' : 𝟚ᴹ ≃ᴹ 𝟚ᴹ'
𝟚ᴹ≃ᴹ𝟚ᴹ' = complement-≃ , I
 where
  I : (x : 𝟚) → 𝟚-cases 𝟘ᴹ 𝟙ᴹ x ≃ᴹ 𝟚-cases 𝟙ᴹ 𝟘ᴹ (⌜ complement-≃ ⌝ x)
  I ₀ = ≃ᴹ-refl 𝟘ᴹ
  I ₁ = ≃ᴹ-refl 𝟙ᴹ

𝟚ᴹ＝𝟚ᴹ' : 𝟚ᴹ ＝ 𝟚ᴹ'
𝟚ᴹ＝𝟚ᴹ' = ⌜ 𝕄-＝-≃ ua 𝟚ᴹ 𝟚ᴹ' ⌝⁻¹ 𝟚ᴹ≃ᴹ𝟚ᴹ'

\end{code}
