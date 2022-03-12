Martin Escardo 7th December 2018.

Characterization of equality in the lifting via the structure of
identity principle.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT

module LiftingIdentityViaSIP
        (𝓣 : Universe)
        {𝓤 : Universe}
        {X : 𝓤 ̇ }
       where

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Univalence
open import UF-UA-FunExt
open import UF-StructureIdentityPrinciple

open import Lifting 𝓣

_⋍_ : 𝓛 X → 𝓛 X → 𝓣 ⊔ 𝓤 ̇
l ⋍ m = Σ e ꞉ is-defined l ≃ is-defined m , value l ≡ value m ∘ ⌜ e ⌝

𝓛-Id : is-univalent 𝓣 → (l m : 𝓛 X) → (l ≡ m) ≃ (l ⋍ m)
𝓛-Id ua = ≡-is-≃ₛ'
 where
  open gsip-with-axioms'
        𝓣 (𝓣 ⊔ 𝓤) (𝓣 ⊔ 𝓤) 𝓣 ua
        (λ P → P → X)
        (λ P s → is-prop P)
        (λ P s → being-prop-is-prop (univalence-gives-funext ua))
        (λ {l m (f , e) → pr₂ l ≡ pr₂ m ∘ f})
        (λ l → refl)
        (λ P ε δ → id)
        (λ A τ υ → refl-left-neutral)

⋍-gives-≡ : is-univalent 𝓣 → {l m : 𝓛 X} → (l ⋍ m) → l ≡ m
⋍-gives-≡ ua = ⌜ 𝓛-Id ua _ _ ⌝⁻¹

\end{code}

When dealing with functions it is often more convenient to work with
pointwise equality, and hence we also consider:

\begin{code}

_⋍·_ : 𝓛 X → 𝓛 X → 𝓣 ⊔ 𝓤 ̇
l ⋍· m = Σ e ꞉ is-defined l ≃ is-defined m , value l ∼ value m ∘ ⌜ e ⌝

𝓛-Id· : is-univalent 𝓣
      → funext 𝓣 𝓤
      → (l m : 𝓛 X) → (l ≡ m) ≃ (l ⋍· m)
𝓛-Id· ua fe l m = (𝓛-Id ua l m) ● (Σ-cong (λ e → ≃-funext fe (value l) (value m ∘ ⌜ e ⌝)))

\end{code}
