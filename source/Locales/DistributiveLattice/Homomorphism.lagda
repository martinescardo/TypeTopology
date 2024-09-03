---
title:        Homomorphisms of distributive lattices
author:       Ayberk Tosun
date-started: 2024-02-21
dates-updated: [2024-05-20, 2024-05-29, 2024-06-09]
---

This module contains the definition of the notion of a distributive lattice
homomorphism.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets

module Locales.DistributiveLattice.Homomorphism
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open import Locales.DistributiveLattice.Definition fe pt
open import Locales.Frame pt fe
open import MLTT.Spartan
open import UF.Base
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.SubtypeClassifier

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_)

\end{code}

The properties of preserving bottom, top, binary joins, and binary meets.

\begin{code}

preserves-𝟎 : (L₁ : DistributiveLattice 𝓤) (L₂ : DistributiveLattice 𝓥)
            → (∣ L₁ ∣ᵈ → ∣ L₂ ∣ᵈ) → Ω 𝓥
preserves-𝟎 L₁ L₂ h = h 𝟎₁ ＝[ σ₂ ]＝ 𝟎₂
 where
  open DistributiveLattice L₁ renaming (𝟎 to 𝟎₁)
  open DistributiveLattice L₂ renaming (𝟎 to 𝟎₂; X-is-set to σ₂)

preserves-𝟏 : (L₁ : DistributiveLattice 𝓤) (L₂ : DistributiveLattice 𝓥)
            → (∣ L₁ ∣ᵈ → ∣ L₂ ∣ᵈ) → Ω 𝓥
preserves-𝟏 L₁ L₂ h = h 𝟏₁ ＝[ σ₂ ]＝ 𝟏₂
 where
  open DistributiveLattice L₁ renaming (𝟏 to 𝟏₁)
  open DistributiveLattice L₂ renaming (𝟏 to 𝟏₂; X-is-set to σ₂)

preserves-∨ : (L₁ : DistributiveLattice 𝓤) (L₂ : DistributiveLattice 𝓥)
            → (∣ L₁ ∣ᵈ → ∣ L₂ ∣ᵈ)
            → Ω (𝓤 ⊔ 𝓥)
preserves-∨ L₁ L₂ h =
 Ɐ x ꞉ ∣ L₁ ∣ᵈ , Ɐ y ꞉ ∣ L₁ ∣ᵈ , h (x ∨₁ y) ＝[ σ ]＝ (h x ∨₂ h y)
  where
   open DistributiveLattice L₁ renaming (_∨_ to _∨₁_)
   open DistributiveLattice L₂ renaming (_∨_ to _∨₂_; X-is-set to σ)

preserves-∧ : (L₁ : DistributiveLattice 𝓤) (L₂ : DistributiveLattice 𝓥)
            → (∣ L₁ ∣ᵈ → ∣ L₂ ∣ᵈ)
            → Ω (𝓤 ⊔ 𝓥)
preserves-∧ L₁ L₂ h =
 Ɐ x ꞉ ∣ L₁ ∣ᵈ , Ɐ y ꞉ ∣ L₁ ∣ᵈ , h (x ∧₁ y) ＝[ σ ]＝ (h x ∧₂ h y)
  where
   open DistributiveLattice L₁ renaming (_∧_ to _∧₁_)
   open DistributiveLattice L₂ renaming (_∧_ to _∧₂_; X-is-set to σ)

\end{code}

The property of being a homomorphism of distributive lattices.

\begin{code}


is-homomorphismᵈ : (L₁ : DistributiveLattice 𝓤) (L₂ : DistributiveLattice 𝓥)
                 → (∣ L₁ ∣ᵈ → ∣ L₂ ∣ᵈ) → Ω (𝓤 ⊔ 𝓥)
is-homomorphismᵈ L₁ L₂ h =  preserves-𝟏 L₁ L₂ h
                         ∧ₚ preserves-∧ L₁ L₂ h
                         ∧ₚ preserves-𝟎 L₁ L₂ h
                         ∧ₚ preserves-∨ L₁ L₂ h


\end{code}

Record-based definition of distributive lattice homomorphisms.

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

 h-is-monotone : is-monotonic (poset-ofᵈ L₁) (poset-ofᵈ L₂) h holds
 h-is-monotone (x , y) p = h x ∧₂ h y   ＝⟨ Ⅰ ⟩
                           h (x ∧₁ y)   ＝⟨ Ⅱ ⟩
                           h x          ∎
  where
   open DistributiveLattice L₁ renaming (_∧_ to _∧₁_)
   open DistributiveLattice L₂ renaming (_∧_ to _∧₂_)

   Ⅰ = h-preserves-∧ x y ⁻¹
   Ⅱ = ap h p

\end{code}

Added on 2024-03-04.

\begin{code}

syntax Homomorphismᵈᵣ L₁ L₂ = L₁ ─d→ L₂

\end{code}

Added on 2024-05-20.

\begin{code}

funᵈ : (K : DistributiveLattice 𝓤) (L : DistributiveLattice 𝓥) → K ─d→ L → ∣ K ∣ᵈ → ∣ L ∣ᵈ
funᵈ K L 𝒽 = Homomorphismᵈᵣ.h {L₁ = K} {L₂ = L} 𝒽

\end{code}

Added on 2024-05-29.

If the underlying functions of two lattice homomorphisms are equal, then they
are equal.

\begin{code}

to-homomorphismᵈ-＝ : (K : DistributiveLattice 𝓤) (L : DistributiveLattice 𝓥)
                      (h₁ h₂ : K ─d→ L)
                    → (funᵈ K L h₁ ∼ funᵈ K L h₂)
                    → h₁ ＝ h₂
to-homomorphismᵈ-＝ K L 𝒽₁ 𝒽₂ φ = † (dfunext fe φ)
 where
  open Homomorphismᵈᵣ 𝒽₁
   using ()
   renaming (h to h₁; h-is-homomorphism to h₁-is-homomorphism)
  open Homomorphismᵈᵣ 𝒽₂
   using ()
   renaming (h to h₂; h-is-homomorphism to h₂-is-homomorphism)

  f : is-homomorphismᵈ K L h₁ holds → Homomorphismᵈᵣ K L
  f ϑ = record { h = h₁ ; h-is-homomorphism = ϑ }

  † : funᵈ K L 𝒽₁ ＝ funᵈ K L 𝒽₂ → 𝒽₁ ＝ 𝒽₂
  † refl = ap f p
   where
    p : h₁-is-homomorphism ＝ h₂-is-homomorphism
    p = holds-is-prop
         (is-homomorphismᵈ K L h₁)
         h₁-is-homomorphism
         h₂-is-homomorphism

\end{code}

Added on 2024-06-09.

\begin{code}

meet-preserving-implies-monotone
 : (K L : DistributiveLattice 𝓤)
 → (f : ∣ K ∣ᵈ → ∣ L ∣ᵈ)
 → (preserves-∧ K L f ⇒ is-monotonic (poset-ofᵈ K) (poset-ofᵈ L) f) holds
meet-preserving-implies-monotone K L f φ (x , y) p =
 f x ∧₂ f y    ＝⟨ Ⅰ ⟩
 f (x ∧₁ y)    ＝⟨ Ⅱ ⟩
 f x           ∎
  where
   open DistributiveLattice K renaming (_∧_ to _∧₁_)
   open DistributiveLattice L renaming (_∧_ to _∧₂_)

   Ⅰ = φ x y ⁻¹
   Ⅱ = ap f p

\end{code}

End of addition.
