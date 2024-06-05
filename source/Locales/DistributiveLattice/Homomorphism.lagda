---
title:       Homomorphisms of distributive lattices
author:      Ayberk Tosun
start-date:  2024-02-21
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets

module Locales.DistributiveLattice.Homomorphism
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open import Locales.Frame pt fe
open import MLTT.Spartan
open import UF.Base
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.SubtypeClassifier
open import Locales.DistributiveLattice.Definition fe pt

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_)

\end{code}

\begin{code}

preserves-𝟎 : (L₁ : DistributiveLattice 𝓤) (L₂ : DistributiveLattice 𝓥)
            → (∣ L₁ ∣ᵈ → ∣ L₂ ∣ᵈ) → Ω 𝓥
preserves-𝟎 L₁ L₂ h = h 𝟎₁ ＝[ σ₂ ]＝ 𝟎₂
 where
  open DistributiveLattice L₁ renaming (𝟎 to 𝟎₁)
  open DistributiveLattice L₂ renaming (𝟎 to 𝟎₂; X-is-set to σ₂)

\end{code}

\begin{code}

preserves-𝟏 : (L₁ : DistributiveLattice 𝓤) (L₂ : DistributiveLattice 𝓥)
            → (∣ L₁ ∣ᵈ → ∣ L₂ ∣ᵈ) → Ω 𝓥
preserves-𝟏 L₁ L₂ h = h 𝟏₁ ＝[ σ₂ ]＝ 𝟏₂
 where
  open DistributiveLattice L₁ renaming (𝟏 to 𝟏₁)
  open DistributiveLattice L₂ renaming (𝟏 to 𝟏₂; X-is-set to σ₂)

\end{code}

\begin{code}

preserves-∨ : (L₁ : DistributiveLattice 𝓤) (L₂ : DistributiveLattice 𝓥)
            → (∣ L₁ ∣ᵈ → ∣ L₂ ∣ᵈ)
            → Ω (𝓤 ⊔ 𝓥)
preserves-∨ L₁ L₂ h =
 Ɐ x ꞉ ∣ L₁ ∣ᵈ , Ɐ y ꞉ ∣ L₁ ∣ᵈ , h (x ∨₁ y) ＝[ σ ]＝ (h x ∨₂ h y)
  where
   open DistributiveLattice L₁ renaming (_∨_ to _∨₁_)
   open DistributiveLattice L₂ renaming (_∨_ to _∨₂_; X-is-set to σ)

\end{code}

\begin{code}

preserves-∧ : (L₁ : DistributiveLattice 𝓤) (L₂ : DistributiveLattice 𝓥)
            → (∣ L₁ ∣ᵈ → ∣ L₂ ∣ᵈ)
            → Ω (𝓤 ⊔ 𝓥)
preserves-∧ L₁ L₂ h =
 Ɐ x ꞉ ∣ L₁ ∣ᵈ , Ɐ y ꞉ ∣ L₁ ∣ᵈ , h (x ∧₁ y) ＝[ σ ]＝ (h x ∧₂ h y)
  where
   open DistributiveLattice L₁ renaming (_∧_ to _∧₁_)
   open DistributiveLattice L₂ renaming (_∧_ to _∧₂_; X-is-set to σ)

\end{code}

\begin{code}


is-homomorphismᵈ : (L₁ : DistributiveLattice 𝓤) (L₂ : DistributiveLattice 𝓥)
                 → (∣ L₁ ∣ᵈ → ∣ L₂ ∣ᵈ) → Ω (𝓤 ⊔ 𝓥)
is-homomorphismᵈ L₁ L₂ h =  preserves-𝟏 L₁ L₂ h
                         ∧ₚ preserves-∧ L₁ L₂ h
                         ∧ₚ preserves-𝟎 L₁ L₂ h
                         ∧ₚ preserves-∨ L₁ L₂ h


\end{code}

\begin{code}

record Homomorphismᵈᵣ (L₁ : DistributiveLattice 𝓤) (L₂ : DistributiveLattice 𝓥) : 𝓤 ⊔ 𝓥  ̇ where
 field
  h                 : ∣ L₁ ∣ᵈ → ∣ L₂ ∣ᵈ
  h-is-homomorphism : is-homomorphismᵈ L₁ L₂ h holds

 h-preserves-𝟏 : preserves-𝟏 L₁ L₂ h holds
 h-preserves-𝟏 = pr₁ h-is-homomorphism

 h-preserves-∧ : preserves-∧ L₁ L₂ h holds
 h-preserves-∧ = pr₁ (pr₂ h-is-homomorphism)

 h-preserves-𝟎 : preserves-𝟎 L₁ L₂ h holds
 h-preserves-𝟎 = pr₁ (pr₂ (pr₂ h-is-homomorphism))

 h-preserves-∨ : preserves-∨ L₁ L₂ h holds
 h-preserves-∨ = pr₂ (pr₂ (pr₂ h-is-homomorphism))

\end{code}

Added on 2024-03-04.

\begin{code}

syntax Homomorphismᵈᵣ L₁ L₂ = L₁ ─d→ L₂

\end{code}
