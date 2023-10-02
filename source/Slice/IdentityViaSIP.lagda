Martin Escardo, 6th December 2018

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

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
open import UF.StructureIdentityPrinciple

open import Slice.Slice 𝓣

_⋍_ : 𝓕 X → 𝓕 X → 𝓣 ⊔ 𝓤 ̇
l ⋍ m = Σ e ꞉ source l ≃ source m , family l ＝ family m ∘ ⌜ e ⌝

S : 𝓣 ̇  → 𝓣 ⊔ 𝓤 ̇
S P = P → X

S-equiv : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓣 ⊔ 𝓤 ̇
S-equiv l m (f , e) = family l ＝ family m ∘ f

S-refl : (A : Σ S) → S-equiv A A (≃-refl ⟨ A ⟩)
S-refl l = refl

S-id-structure : (X : 𝓣 ̇ ) (s t : S X)
                → S-equiv (X , s) (X , t) (≃-refl X) → s ＝ t
S-id-structure _ _ _ = id

S-transport : (A : Σ S)
               (s : S ⟨ A ⟩)
               (υ : S-equiv A (⟨ A ⟩ , s) (≃-refl ⟨ A ⟩))
             → transport
                  (λ - → S-equiv A (⟨ A ⟩ , -) (≃-refl ⟨ A ⟩))
                  (S-id-structure ⟨ A ⟩ (structure A) s υ)
                  (S-refl A)
             ＝ υ
S-transport _ _ refl = refl

𝓕-Id : is-univalent 𝓣 → (l m : 𝓕 X) → (l ＝ m) ≃ (l ⋍ m)
𝓕-Id ua = ＝-is-≃ₛ'
 where
  open gsip
        𝓣 (𝓣 ⊔ 𝓤) ua
        (λ P → P → X)
        (λ {l m (f , e) → family l ＝ family m ∘ f})
        (λ l → refl)
        (λ P ε δ → id)
        S-transport --S-transport -- (λ A τ υ → refl-left-neutral)

⋍-gives-＝ : is-univalent 𝓣 → {l m : 𝓕 X} → (l ⋍ m) → l ＝ m
⋍-gives-＝ ua = ⌜ 𝓕-Id ua _ _ ⌝⁻¹

_⋍·_ : 𝓕 X → 𝓕 X → 𝓣 ⊔ 𝓤 ̇
l ⋍· m = Σ e ꞉ source l ≃ source m , family l ∼ family m ∘ ⌜ e ⌝

𝓕-Id· : is-univalent 𝓣
      → funext 𝓣 𝓤
      → (l m : 𝓕 X) → (l ＝ m) ≃ (l ⋍· m)
𝓕-Id· ua fe l m = (𝓕-Id ua l m) ● (Σ-cong (λ e → ≃-funext fe (family l) (family m ∘ ⌜ e ⌝)))

\end{code}
