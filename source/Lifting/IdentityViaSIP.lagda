Martin Escardo 7th December 2018.

Characterization of equality in the lifting via the structure of
identity principle.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan

module Lifting.IdentityViaSIP
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

open import Lifting.Lifting 𝓣

_⋍_ : 𝓛 X → 𝓛 X → 𝓣 ⊔ 𝓤 ̇
l ⋍ m = Σ e ꞉ is-defined l ≃ is-defined m , value l ＝ value m ∘ ⌜ e ⌝

S : 𝓣 ̇  → 𝓣 ⊔ 𝓤 ̇
S P = P → X

S-equiv : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓣 ⊔ 𝓤 ̇
S-equiv l m (f , e) = pr₂ l ＝ pr₂ m ∘ f

S-refl : (A : Σ S) → S-equiv A A (≃-refl ⟨ A ⟩)
S-refl A = refl

S-id-structure : (X : 𝓣  ̇) (s t : S X)
               → S-equiv (X , s) (X , t) (≃-refl X) → s ＝ t
S-id-structure X s t = id

S-transport : (A : Σ S)
                (s : S ⟨ A ⟩)
                (υ : S-equiv A (⟨ A ⟩ , s) (≃-refl ⟨ A ⟩))
              → transport
                   (λ - → S-equiv A (⟨ A ⟩ , -) (≃-refl ⟨ A ⟩))
                   (S-id-structure ⟨ A ⟩ (structure A) s υ)
                   (S-refl A)
              ＝ υ
S-transport A s refl = refl

𝓛-Id : is-univalent 𝓣 → (l m : 𝓛 X) → (l ＝ m) ≃ (l ⋍ m)
𝓛-Id ua = ＝-is-≃ₛ'
 where
  open gsip-with-axioms'
        𝓣 (𝓣 ⊔ 𝓤) (𝓣 ⊔ 𝓤) 𝓣 ua
        (λ P → P → X)
        (λ P s → is-prop P)
        (λ P s → being-prop-is-prop (univalence-gives-funext ua))
        S-equiv -- (λ {l m (f , e) → pr₂ l ＝ pr₂ m ∘ f})
        (λ l → refl)
        (λ P ε δ → id)
        S-transport

⋍-gives-＝ : is-univalent 𝓣 → {l m : 𝓛 X} → (l ⋍ m) → l ＝ m
⋍-gives-＝ ua = ⌜ 𝓛-Id ua _ _ ⌝⁻¹

\end{code}

When dealing with functions it is often more convenient to work with
pointwise equality, and hence we also consider:

\begin{code}

_⋍·_ : 𝓛 X → 𝓛 X → 𝓣 ⊔ 𝓤 ̇
l ⋍· m = Σ e ꞉ is-defined l ≃ is-defined m , value l ∼ value m ∘ ⌜ e ⌝

𝓛-Id· : is-univalent 𝓣
      → funext 𝓣 𝓤
      → (l m : 𝓛 X) → (l ＝ m) ≃ (l ⋍· m)
𝓛-Id· ua fe l m = (𝓛-Id ua l m) ● (Σ-cong (λ e → ≃-funext fe (value l) (value m ∘ ⌜ e ⌝)))

\end{code}
