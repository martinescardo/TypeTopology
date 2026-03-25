Martin Escardo, 6th December 2018

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module Slice.IdentityViaSIP
        (𝓣 : Universe)
        {𝓤 : Universe}
        {X : 𝓤 ̇ }
       where

open import UF.Base
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Univalence
open import UF.UA-FunExt
open import deprecated.StructureIdentityPrinciple

open import Slice.Construction 𝓣

_⋍_ : 𝓕 X → 𝓕 X → 𝓣 ⊔ 𝓤 ̇
l ⋍ m = Σ e ꞉ source l ≃ source m , family l ＝ family m ∘ ⌜ e ⌝

𝓕-Id : is-univalent 𝓣 → (l m : 𝓕 X) → (l ＝ m) ≃ (l ⋍ m)
𝓕-Id ua = ＝-is-≃ₛ'
 where
  open gsip
        𝓣 (𝓣 ⊔ 𝓤) ua
        (λ P → P → X)
        (λ {l m (f , e) → family l ＝ family m ∘ f})
        (λ l → refl)
        (λ P ε δ → id)
        (λ A τ υ → refl-left-neutral)

⋍-gives-＝ : is-univalent 𝓣 → {l m : 𝓕 X} → (l ⋍ m) → l ＝ m
⋍-gives-＝ ua = ⌜ 𝓕-Id ua _ _ ⌝⁻¹

_⋍·_ : 𝓕 X → 𝓕 X → 𝓣 ⊔ 𝓤 ̇
l ⋍· m = Σ e ꞉ source l ≃ source m , family l ∼ family m ∘ ⌜ e ⌝

𝓕-Id· : is-univalent 𝓣
      → funext 𝓣 𝓤
      → (l m : 𝓕 X) → (l ＝ m) ≃ (l ⋍· m)
𝓕-Id· ua fe l m = (𝓕-Id ua l m) ● (Σ-cong (λ e → ≃-funext fe (family l) (family m ∘ ⌜ e ⌝)))

\end{code}
