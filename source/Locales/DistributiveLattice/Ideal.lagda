---
title:       Ideals of distributive lattices
author:      Ayberk Tosun
start-date:  2024-02-14
---

This module contains the definition of the notion of ideal over a distributive
lattice.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
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
open import MLTT.List
open import MLTT.Spartan
open import UF.Base
open import UF.Equiv hiding (_■)
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.SubtypeClassifier

open AllCombinators pt fe hiding (_∨_)
open PropositionalTruncation pt hiding (_∨_)

\end{code}

The type of ideals of a distributive lattice.

\begin{code}

is-inhabited : (L : DistributiveLattice 𝓤) → 𝓟 {𝓥} ∣ L ∣ᵈ → Ω (𝓤 ⊔ 𝓥)
is-inhabited L S = Ǝ x ꞉ ∣ L ∣ᵈ , x ∈ S

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
  I-is-inhabited       : is-inhabited L I holds
  I-is-downward-closed : is-downward-closed L I holds
  I-is-closed-under-∨  : is-closed-under-binary-joins L I holds

 I-contains-𝟎 : (𝟎 ∈ₚ I) holds
 I-contains-𝟎 = ∥∥-rec (holds-is-prop (𝟎 ∈ₚ I)) † I-is-inhabited
  where
   † : Σ x ꞉ X , (x ∈ₚ I) holds → 𝟎 ∈ I
   † (x , p) = I-is-downward-closed 𝟎 x (𝟎ᵈ-is-bottom L x) p

module IdealNotation (L : DistributiveLattice 𝓤)  where

 _∈ᵢ_ : ∣ L ∣ᵈ → Ideal L → Ω 𝓤
 x ∈ᵢ ℐ = Ideal.I ℐ x

 infix 30 _∈ᵢ_

 _∈ⁱ_ : ∣ L ∣ᵈ → Ideal L → 𝓤 ̇
 x ∈ⁱ ℐ = (x ∈ᵢ ℐ) holds

is-ideal : (L : DistributiveLattice 𝓤) → 𝓟 {𝓤} ∣ L ∣ᵈ → Ω 𝓤
is-ideal L I =
 is-inhabited L I ∧ is-downward-closed L I ∧ is-closed-under-binary-joins L I

Ideal₀ : DistributiveLattice 𝓤 → 𝓤 ⁺  ̇
Ideal₀ {𝓤} L = Σ I ꞉ 𝓟 {𝓤} ∣ L ∣ᵈ , is-ideal L I holds

to-ideal₀ : (L : DistributiveLattice 𝓤) → Ideal L → Ideal₀ L
to-ideal₀ L ℐ = I , I-is-inhabited , I-is-downward-closed , I-is-closed-under-∨
 where
  open Ideal ℐ

to-ideal : (L : DistributiveLattice 𝓤) → Ideal₀ L → Ideal L
to-ideal L ℐ@(I , ι , δ , ν) = record
                                { I                    = I
                                ; I-is-inhabited       = ι
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
  open Ideal I₁ renaming (I to I₁′)
  open Ideal I₂ renaming (I to I₂′)

  q : (x : ∣ L ∣ᵈ) → I₁′ x ＝ I₂′ x
  q x = to-subtype-＝
         (λ _ → being-prop-is-prop fe)
         (pe (holds-is-prop (x ∈ₚ I₁′)) (holds-is-prop (x ∈ₚ I₂′)) (φ x) (ψ x))

  ‡ : to-ideal₀ L I₁ ＝ to-ideal₀ L I₂
  ‡ = to-subtype-＝ (λ I → holds-is-prop (is-ideal L I)) (dfunext fe q)

  † = ap (to-ideal L) ‡

\end{code}

Closed under finite joins.

\begin{code}

module _ (L : DistributiveLattice 𝓤) (I : Ideal L) where

 open IdealNotation L
 open Ideal I hiding (I)

 ideals-are-closed-under-finite-joins : (xs : List ∣ L ∣ᵈ)
                                      → (((x , _) : type-from-list xs) → (x ∈ᵢ I) holds)
                                      → (join-listᵈ L xs ∈ᵢ I) holds
 ideals-are-closed-under-finite-joins []       φ = I-contains-𝟎
 ideals-are-closed-under-finite-joins (x ∷ xs) φ =
  I-is-closed-under-∨ x (join-listᵈ L xs) (φ (x , in-head)) IH
   where
    † : (k : type-from-list xs) → (pr₁ k ∈ᵢ I) holds
    † (k , r) = φ (k , in-tail r)

    IH : (join-listᵈ L xs ∈ᵢ I) holds
    IH = ideals-are-closed-under-finite-joins xs †

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
   record
    { I                    = down-closure x
    ; I-is-inhabited       = ∣ x , ≤-is-reflexive (poset-ofᵈ L) x ∣
    ; I-is-downward-closed = †
    ; I-is-closed-under-∨  = ‡
    }

\end{code}

Some nice syntax. Tried turning this into a definition with the same precedence,
but it doesn't seem to work.


\begin{code}

 syntax principal-ideal x = ↓ x

 infix 32 principal-ideal

\end{code}
