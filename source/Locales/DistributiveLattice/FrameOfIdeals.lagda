---
title:       Ideals of distributive lattices
author:      Ayberk Tosun
start-date:  2024-02-21
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons

module Locales.DistributiveLattice.FrameOfIdeals
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Ideal pt fe pe
open import Locales.Frame pt fe
open import UF.Powerset-MultiUniverse
open import MLTT.Spartan
open import UF.Base
open import UF.SubtypeClassifier
open import UF.Logic
open import Slice.Family

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)

open PropositionalSubsetInclusionNotation fe

open PropositionalTruncation pt hiding (_∨_)

\end{code}

\begin{code}

module DefnOfFrameOfIdeal (L : DistributiveLattice 𝓤) where

 open DistributiveLattice L

 _⊆ᵢ_ : Ideal L → Ideal L → Ω (𝓤)
 ℐ₁ ⊆ᵢ ℐ₂ = Ɐ x ꞉ ∣ L ∣ᵈ , x ∈ₚ I₁ ⇒ x ∈ₚ I₂
  where
   open Ideal ℐ₁ renaming (I to I₁)
   open Ideal ℐ₂ renaming (I to I₂)

 ⊆ᵢ-is-reflexive : (I : Ideal L) → (I ⊆ᵢ I) holds
 ⊆ᵢ-is-reflexive _ _ = id

 ⊆ᵢ-is-transitive : (I₁ I₂ I₃ : Ideal L) → (I₁ ⊆ᵢ I₂ ⇒ I₂ ⊆ᵢ I₃ ⇒ I₁ ⊆ᵢ I₃) holds
 ⊆ᵢ-is-transitive I₁ I₂ I₃ p q x r = q x (p x r)

 ⊆ᵢ-is-antisymmetric : (I₁ I₂ : Ideal L) → (I₁ ⊆ᵢ I₂) holds → (I₂ ⊆ᵢ I₁) holds → I₁ ＝ I₂
 ⊆ᵢ-is-antisymmetric = ideal-extensionality L

 poset-of-ideals : Poset (𝓤 ⁺) 𝓤
 poset-of-ideals = (Ideal L)
                 , _⊆ᵢ_
                 , (⊆ᵢ-is-reflexive  , ⊆ᵢ-is-transitive)
                 , ⊆ᵢ-is-antisymmetric _ _

\end{code}

The top ideal.

\begin{code}

 open PrincipalIdeals L

 𝟏ᵢ : Ideal L
 𝟏ᵢ = principal-ideal 𝟏

 𝟏ᵢ-is-top : (I : Ideal L) → (I ⊆ᵢ 𝟏ᵢ) holds
 𝟏ᵢ-is-top I x _ = 𝟏ᵈ-is-top L x

\end{code}

\begin{code}

 _∧ᵢ_ : Ideal L → Ideal L → Ideal L
 ℐ₁ ∧ᵢ ℐ₂ =
  record
   { I                    = I₁ ∩ I₂
   ; I-is-downward-closed = †
   ; I-is-closed-under-∨  = ‡
   }
  where
   open Ideal ℐ₁ renaming (I to I₁)
   open Ideal ℐ₂ renaming (I to I₂)

   † : is-downward-closed L (I₁ ∩ I₂) holds
   † x y p (q₁ , q₂) = Ideal.I-is-downward-closed ℐ₁ x y p q₁
                     , Ideal.I-is-downward-closed ℐ₂ x y p q₂

   ‡ : is-closed-under-binary-joins L (I₁ ∩ I₂) holds
   ‡ x y (p₁ , p₂) (q₁ , q₂) = Ideal.I-is-closed-under-∨ ℐ₁ x y p₁ q₁
                             , Ideal.I-is-closed-under-∨ ℐ₂ x y p₂ q₂

\end{code}

\begin{code}

 open Meets _⊆ᵢ_

 ∧ᵢ-is-lower : (I₁ I₂ : Ideal L)
             → ((I₁ ∧ᵢ I₂) is-a-lower-bound-of (I₁ , I₂)) holds
 ∧ᵢ-is-lower I₁ I₂ = (λ _ → pr₁) , (λ _ → pr₂)

 ∧ᵢ-is-greatest : (I₁ I₂ I₃ : Ideal L)
                → (I₃ is-a-lower-bound-of (I₁ , I₂) ⇒ I₃ ⊆ᵢ (I₁ ∧ᵢ I₂)) holds
 ∧ᵢ-is-greatest I₁ I₂ I₃ (φ , ψ) x p = φ x p , ψ x p

 ∧ᵢ-is-glb : (I₁ I₂ : Ideal L) → ((I₁ ∧ᵢ I₂) is-glb-of (I₁ , I₂)) holds
 ∧ᵢ-is-glb I₁ I₂ = ∧ᵢ-is-lower I₁ I₂ , λ { (I₃ , p) → ∧ᵢ-is-greatest I₁ I₂ I₃ p }

\end{code}

\begin{code}

 open IdealNotation L

 ⋁ᵢ_ : Fam 𝓤 (Ideal L) → Ideal L
 ⋁ᵢ S =
  record
   { I                    = ⋃S
   ; I-is-downward-closed = †
   ; I-is-closed-under-∨  = ‡
   }
   where
    ⋃S : ∣ L ∣ᵈ → Ω 𝓤
    ⋃S = λ x →  Ǝ i ꞉ index S , x ∈ⁱ (S [ i ])

    † : is-downward-closed L ⋃S holds
    † x y p = ∥∥-rec (holds-is-prop (⋃S x)) γ
     where
      γ : Σ i ꞉ (index S) , y ∈ⁱ (S [ i ]) → ⋃S x holds
      γ (i , q) = ∣ i , Sᵢ-is-downward-closed x y p q ∣
       where
        open Ideal (S [ i ]) using () renaming (I-is-downward-closed to Sᵢ-is-downward-closed)

    foo : ∣ L ∣ᵈ ＝ X
    foo = refl

    ‡ : is-closed-under-binary-joins L ⋃S holds
    ‡ x y p q = ∥∥-rec (holds-is-prop ((x ∨ y) ∈ₚ ⋃S)) γ β
     where
      β : (x ∧ y) ∈ ⋃S
      β = † (x ∧ y) x (∧-is-a-lower-bound₁ L x y) p

      γ : (Σ i ꞉ index S , (x ∧ y) ∈ⁱ (S [ i ])) → ⋃S (x ∨ y) holds
      γ (i , r) = {!!}
       where
       open Ideal (S [ i ]) using () renaming (I-is-downward-closed to Sᵢ-is-downward-closed)

\end{code}
