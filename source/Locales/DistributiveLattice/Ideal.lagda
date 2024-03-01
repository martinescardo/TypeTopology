---
title:       Ideals of distributive lattices
author:      Ayberk Tosun
start-date:  2024-02-14
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Locales.DistributiveLattice.Ideal
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Properties fe pt
open import Locales.Frame pt fe
open import UF.Powerset-MultiUniverse
open import MLTT.Spartan
open import UF.Base
open import UF.SubtypeClassifier
open import UF.Logic
open import UF.Equiv hiding (_■)

open AllCombinators pt fe hiding (_∨_)

\end{code}

The type of ideals of a distributive lattice.

\begin{code}

is-downward-closed : (L : DistributiveLattice 𝓤) → 𝓟 {𝓥} ∣ L ∣ᵈ → Ω (𝓤 ⊔ 𝓥)
is-downward-closed L I =
 Ɐ x ꞉ ∣ L ∣ᵈ , Ɐ y ꞉ ∣ L ∣ᵈ , x ≤ᵈ[ L ] y ⇒ y ∈ₚ I ⇒ x ∈ₚ I
  where
   open DistributiveLattice L

is-closed-under-binary-joins : (L : DistributiveLattice 𝓤)
                             → 𝓟 {𝓥} ∣ L ∣ᵈ → Ω (𝓤 ⊔ 𝓥)
is-closed-under-binary-joins L I =
 Ɐ x ꞉ ∣ L ∣ᵈ , Ɐ y ꞉ ∣ L ∣ᵈ , x ∈ₚ I ⇒ y ∈ₚ I ⇒ (x ∨ y) ∈ₚ I
  where
   open DistributiveLattice L

record Ideal (L : DistributiveLattice 𝓤) : 𝓤 ⁺  ̇ where
 open DistributiveLattice L

 field
  I : 𝓟 {𝓤} ∣ L ∣ᵈ
  I-is-downward-closed : is-downward-closed L I holds
  I-is-closed-under-∨  : is-closed-under-binary-joins L I holds

module IdealNotation (L : DistributiveLattice 𝓤)  where

 _∈ᵢ_ : ∣ L ∣ᵈ → Ideal L → Ω 𝓤
 x ∈ᵢ ℐ = Ideal.I ℐ x

 _∈ⁱ_ : ∣ L ∣ᵈ → Ideal L → 𝓤 ̇
 x ∈ⁱ ℐ = (x ∈ᵢ ℐ) holds

is-ideal : (L : DistributiveLattice 𝓤) → 𝓟 {𝓤} ∣ L ∣ᵈ → Ω 𝓤
is-ideal L I = is-downward-closed L I ∧ is-closed-under-binary-joins L I

Ideal₀ : DistributiveLattice 𝓤 → 𝓤 ⁺  ̇
Ideal₀ {𝓤} L =
 Σ I ꞉ 𝓟 {𝓤} ∣ L ∣ᵈ ,
  (is-downward-closed L I ∧ is-closed-under-binary-joins L I) holds

to-ideal₀ : (L : DistributiveLattice 𝓤) → Ideal L → Ideal₀ L
to-ideal₀ L ℐ = I , I-is-downward-closed , I-is-closed-under-∨
 where
  open Ideal ℐ

to-ideal : (L : DistributiveLattice 𝓤) → Ideal₀ L → Ideal L
to-ideal L ℐ@(I , δ , ν) = record { I                    = I
                                  ; I-is-downward-closed = δ
                                  ; I-is-closed-under-∨  = ν
                                  }

ideal-equiv-ideal₀ : (L : DistributiveLattice 𝓤) → (Ideal L) ≃ (Ideal₀ L)
ideal-equiv-ideal₀ L =
 (to-ideal₀ L) , (to-ideal L , λ _ → refl) , (to-ideal L) , λ _ → refl

ideal-extensionality : (L : DistributiveLattice 𝓤)
                     → (I₁ I₂ : Ideal L)
                     → Ideal.I I₁ ⊆ Ideal.I I₂
                     → Ideal.I I₂ ⊆ Ideal.I I₁
                     → I₁ ＝ I₂
ideal-extensionality L I₁ I₂ φ ψ = I₁                          ＝⟨ refl ⟩
                                   to-ideal L (to-ideal₀ L I₁) ＝⟨ † ⟩
                                   to-ideal L (to-ideal₀ L I₂) ＝⟨ refl ⟩
                                   I₂                          ∎
 where
  ‡ : to-ideal₀ L I₁ ＝ to-ideal₀ L I₂
  ‡ = to-subtype-＝
         (λ I → holds-is-prop (is-ideal L I))
         (dfunext fe (λ x → to-subtype-＝ (λ _ → being-prop-is-prop fe) (pe (holds-is-prop (Ideal.I I₁ x)) (holds-is-prop (Ideal.I I₂ x)) (φ x) (ψ x))))

  † = ap (to-ideal L) ‡

\end{code}

The principal ideal.

\begin{code}

module PrincipalIdeals (L : DistributiveLattice 𝓤) where

 open DistributiveLattice L

 down-closure : ∣ L ∣ᵈ → 𝓟 {𝓤} ∣ L ∣ᵈ
 down-closure x = λ y → y ≤ᵈ[ L ] x

 principal-ideal : ∣ L ∣ᵈ → Ideal L
 principal-ideal x =
  let
   open PosetReasoning (poset-ofᵈ L)

   † : is-downward-closed L (down-closure x) holds
   † y z p q = y ≤⟨ p ⟩ z ≤⟨ q ⟩ x ■

   ‡ : is-closed-under-binary-joins L (down-closure x) holds
   ‡ a b c p = ∨-is-least L a b x (c , p)
  in
   record { I                    = down-closure x
          ; I-is-downward-closed = †
          ; I-is-closed-under-∨  = ‡
          }

\end{code}
