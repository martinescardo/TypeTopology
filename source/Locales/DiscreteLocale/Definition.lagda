--------------------------------------------------------------------------------
title:          The discrete locale
author:         Ayberk Tosun
date-started:   2024-03-04
date-completed: 2024-03-04
--------------------------------------------------------------------------------

We define the discrete locale (i.e. the frame of opens of the discrete topology)
over a set `X`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons

module Locales.DiscreteLocale.Definition
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Locales.DistributiveLattice.Definition fe pt
open import Locales.Frame pt fe
open import MLTT.Spartan
open import Slice.Family
open import UF.Logic
open import UF.Sets
open import UF.Powerset
open import UF.SubtypeClassifier

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)
open PropositionalSubsetInclusionNotation fe
open PropositionalTruncation pt hiding (_∨_)

\end{code}

We work with a fixed set `X` in this module.

\begin{code}

module DefnOfDiscreteLocale (X : 𝓤  ̇) (σ : is-set X) where

\end{code}

We start by writing down the poset of subsets of `X`.

\begin{code}

 _⊆ᵖ_ : 𝓟 X → 𝓟 X → Ω 𝓤
 P ⊆ᵖ Q = P ⊆ₚ Q

 infix 30 _⊆ᵖ_

 ⊆-partial-order : is-partial-order (𝓟 X) _⊆ₚ_
 ⊆-partial-order = (⊆-refl , ⊆-trans') , subset-extensionality pe fe

 poset-of-subsets : Poset (𝓤 ⁺) 𝓤
 poset-of-subsets = 𝓟 X
                  , _⊆ₚ_
                  , (⊆-refl , ⊆-trans')
                  , subset-extensionality pe fe

\end{code}

The top element is the full subset, denoted `full`.

\begin{code}

 full-is-top : (P : 𝓟 X) → (P ⊆ₚ full) holds
 full-is-top I x = λ _ → ⋆

\end{code}

Binary meets are set intersection.

\begin{code}

 open Meets _⊆ᵖ_

 ∩-gives-glb : ((P , Q) : 𝓟 X × 𝓟 X) → ((P ∩ Q) is-glb-of (P , Q)) holds
 ∩-gives-glb (P , Q) = ((λ _ → pr₁) , (λ _ → pr₂))
                     , λ (_ , φ , ψ) x r → φ x r , ψ x r

\end{code}

Small joins are given by set union, defined as:

\begin{code}

 ⋁ₚ_ : Fam 𝓤 (𝓟 X) → 𝓟 X
 ⋁ₚ S = λ x → Ǝ k ꞉ index S , x ∈ (S [ k ])

 infix 32 ⋁ₚ_

 open Joins _⊆ᵖ_

 ⋁ₚ-gives-an-upper-bound : (S : Fam 𝓤 (𝓟 X))
                         → ((⋁ₚ S) is-an-upper-bound-of S) holds
 ⋁ₚ-gives-an-upper-bound S i _ μ = ∣ i , μ ∣

 ⋁ₚ-is-least : (S : Fam 𝓤 (𝓟 X)) (U : 𝓟 X)
             → (U is-an-upper-bound-of S) holds
             → (⋁ₚ S) ⊆ U
 ⋁ₚ-is-least S U υ x = ∥∥-rec (holds-is-prop (x ∈ₚ U)) †
  where
   † : Σ i ꞉ index S , x ∈ (S [ i ]) → U x holds
   † (i , μ) = υ i x μ

 ⋁ₚ-gives-lub : (S : Fam 𝓤 (𝓟 X)) → ((⋁ₚ S) is-lub-of S) holds
 ⋁ₚ-gives-lub S = ⋁ₚ-gives-an-upper-bound S
                , λ { (U , υ) → ⋁ₚ-is-least S U υ }

\end{code}

Finally, the distributivity law.

\begin{code}

 distributivityₚ : (P : 𝓟 X) (S : Fam 𝓤 (𝓟 X))
                 → P ∩ (⋁ₚ S) ＝ ⋁ₚ ⁅ P ∩ Q ∣ Q ε S ⁆
 distributivityₚ P S = subset-extensionality pe fe † ‡
  where
   † : (P ∩ ⋁ₚ S) ⊆ᵖ ⋁ₚ ⁅ P ∩ Q ∣ Q ε S ⁆ holds
   † x (p , e) = ∥∥-rec ∥∥-is-prop (λ { (i , q) → ∣ i , (p , q) ∣ }) e

   ‡ : ⋁ₚ ⁅ P ∩ Q ∣ Q ε S ⁆ ⊆ᵖ (P ∩ ⋁ₚ S) holds
   ‡ x = ∥∥-rec (holds-is-prop (x ∈ₚ (P ∩ ⋁ₚ S))) γ
    where
     γ : Σ i ꞉ index S , x ∈ (P ∩ (S [ i ])) → x ∈ (P ∩ (⋁ₚ S))
     γ (i , p , q) = p , ∣ i , q ∣

\end{code}

We package these up into a frame that we call `frame-of-subsets`.

\begin{code}

 frame-of-subsets-structure : frame-structure 𝓤 𝓤 (𝓟 X)
 frame-of-subsets-structure = (_⊆ₚ_ , full , _∩_ , ⋁ₚ_)
                            , ⊆-partial-order
                            , full-is-top
                            , ∩-gives-glb
                            , ⋁ₚ-gives-lub
                            , λ (P , Q) → distributivityₚ P Q

 frame-of-subsets : Frame (𝓤 ⁺) 𝓤 𝓤
 frame-of-subsets = 𝓟 X , frame-of-subsets-structure

\end{code}

The discrete locale on set `X` is the locale given by the frame of subsets of
`X`.

\begin{code}

discrete-locale : (X : 𝓤  ̇) → is-set X → Locale (𝓤 ⁺) 𝓤 𝓤
discrete-locale X σ =
 record
  { ⟨_⟩ₗ         = 𝓟 X
  ; frame-str-of = DefnOfDiscreteLocale.frame-of-subsets-structure X σ
  }

\end{code}
