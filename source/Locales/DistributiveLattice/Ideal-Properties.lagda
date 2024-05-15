--------------------------------------------------------------------------------
title:        Properties of ideals
author:       Ayberk Tosun
date-started: 2024-03-02
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Locales.DistributiveLattice.Ideal-Properties
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Ideal pt fe pe
open import Locales.DistributiveLattice.Properties fe pt
open import Locales.DistributiveLattice.Spectrum fe pe pt
open import Locales.Frame pt fe hiding (is-directed)
open import MLTT.List
open import MLTT.Spartan
open import Slice.Family
open import UF.Base
open import UF.Classifiers
open import UF.Equiv hiding (_■)
open import UF.Logic
open import UF.Powerset-MultiUniverse hiding (𝕋)
open import UF.SubtypeClassifier

open AllCombinators pt fe hiding (_∨_)
open PropositionalTruncation pt hiding (_∨_)

\end{code}

\begin{code}

module IdealProperties (L : DistributiveLattice 𝓤) where

 open DefnOfFrameOfIdeal  L
 open DistributiveLattice L
 open IdealNotation L

 contains-𝟏-implies-above-𝟏 : (I : Ideal L) → 𝟏 ∈ⁱ I → (𝟏ᵢ ⊆ᵢ I) holds
 contains-𝟏-implies-above-𝟏 I μ₁ x μ₂ =
  I-is-downward-closed x 𝟏 (𝟏ᵈ-is-top L x) μ₁
   where
    open Ideal I using (I-is-downward-closed)

 above-𝟏-implies-contains-𝟏 : (I : Ideal L) → (𝟏ᵢ ⊆ᵢ I) holds → 𝟏 ∈ⁱ I
 above-𝟏-implies-contains-𝟏 I φ = φ 𝟏 (≤-is-reflexive (poset-ofᵈ L) 𝟏)

\end{code}

Added on 2024-03-13.

\begin{code}

 open PrincipalIdeals L
 open Joins _⊆ᵢ_

\end{code}

Every ideal is the join of the principal ideals of the elements it contains. To
prove this fact, we start by writing down the family of principal ideals
generated by the elements of a given ideal.

\begin{code}

 principal-ideals-of : (I : Ideal L) → Fam 𝓤 (Ideal L)
 principal-ideals-of I = ⁅ ↓ u ∣ (u , _) ∶ Σ u ꞉ ∣ L ∣ᵈ , u ∈ⁱ I ⁆

\end{code}

Given an ideal `I`, it is clear that it is an upper bound of its family of
principal ideals.

\begin{code}

 ideal-is-an-upper-bound-of-its-principal-ideals
  : (I : Ideal L)
  → (I is-an-upper-bound-of (principal-ideals-of I)) holds
 ideal-is-an-upper-bound-of-its-principal-ideals I (u , μᵢ) x μ =
  I-is-downward-closed x u μ μᵢ
   where
    open Ideal I using (I-is-downward-closed)

\end{code}

It is in fact the _least_ upper bound of this family.

\begin{code}

 ideal-is-lowerbound-of-upperbounds-of-its-principal-ideals
  : (I Iᵤ : Ideal L)
  → (Iᵤ is-an-upper-bound-of (principal-ideals-of I)
  ⇒ (I ⊆ᵢ Iᵤ)) holds
 ideal-is-lowerbound-of-upperbounds-of-its-principal-ideals I Iᵤ φ x μ =
  φ (x , μ) x (≤-is-reflexive (poset-ofᵈ L) x)

\end{code}

Added on 2024-03-28.

\begin{code}

 open import Locales.DirectedFamily pt fe _⊆ᵢ_

 principal-ideals-of-ideal-form-a-directed-family
  : (I : Ideal L)
  → is-directed (principal-ideals-of I) holds
 principal-ideals-of-ideal-form-a-directed-family I =
  ∣ 𝟎 , I-contains-𝟎 ∣ , ‡
   where
    open Ideal I hiding (I)
    open PosetReasoning (poset-ofᵈ L)

    ‡ : is-closed-under-binary-upper-bounds (principal-ideals-of I) holds
    ‡ (x , μ₁) (y , μ₂) = ∣ (x ∨ y , I-is-closed-under-∨ x y μ₁ μ₂) , β , γ ∣
     where
      β : (↓ x ⊆ᵢ ↓ (x ∨ y)) holds
      β z p = z ≤⟨ p ⟩ x ≤⟨ ∨-is-an-upper-bound₁ L x y ⟩ (x ∨ y) ■

      γ : (↓ y ⊆ᵢ ↓ (x ∨ y)) holds
      γ z p = z ≤⟨ p ⟩ y ≤⟨ ∨-is-an-upper-bound₂ L x y ⟩ (x ∨ y) ■

\end{code}

Added on 2024-05-03.

Every ideal is directed.

\begin{code}

 open classifier-single-universe 𝓤

 open import Locales.DirectedFamily pt fe (λ x y → x ≤ᵈ[ L ] y) using () renaming (is-directed to is-directed-L; is-closed-under-binary-upper-bounds to is-closed-under-binary-upper-bounds-L)

 ideals-are-directed : (I : Ideal L)
                     → is-directed-L (𝕋 ∣ L ∣ᵈ (_∈ⁱ I)) holds
 ideals-are-directed I = ∣ 𝟎 , I-contains-𝟎 ∣ , †
  where
   open Ideal I using (I-contains-𝟎; I-is-closed-under-∨)

   † : is-closed-under-binary-upper-bounds-L (𝕋 ∣ L ∣ᵈ (_∈ⁱ I)) holds
   † (x , μ₁) (y , μ₂) = ∣ ((x ∨ y) , I-is-closed-under-∨ x y μ₁ μ₂) , ♣ , ♠ ∣
    where
     ♣ : (x ≤ᵈ[ L ] (x ∨ y)) holds
     ♣ = ∨-is-an-upper-bound₁ L x y

     ♠ : (y ≤ᵈ[ L ] (x ∨ y)) holds
     ♠ = ∨-is-an-upper-bound₂ L x y

\end{code}
