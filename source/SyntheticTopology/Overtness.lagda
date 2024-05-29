---
title:                  Compactness in Synthetic Topology
author:             Martin Trucchi
date-started:  2024-05-28
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import SyntheticTopology.SierpinskiObject 
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.UniverseEmbedding

module SyntheticTopology.Overtness
        (𝓤  𝓥 : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (𝕊 : Generalized-Sierpinski-Object fe pe pt 𝓤 𝓥)
        where

open import UF.ImageAndSurjection pt
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open Sierpinski-notations fe pe pt 𝕊


\end{code}

Overtness

This notion is similar to compactness, in a dual meaning.
A set is overt if the proposition (∃ x , P x) is open whenever P is open.

\begin{code}

is-overt : hSet 𝓤  → Ω (𝓤 ⁺ ⊔ 𝓥)
is-overt (X , sX) =
  Ɐ (P , open-P) ꞉ 𝓞 (X , sX) ,
   is-affirmable (Ǝₚ x ꞉ X , P x)

\end{code}

We prove here, similar to image-of-compact, that image of overt sets are overt. 

\begin{code}

image-of-overt :  ((X , sX) (Y , sY) : hSet 𝓤)
                   → (f : X → Y)
                   → is-surjection f
                   → is-overt (X , sX) holds
                   → is-overt (Y , sY) holds
                   
image-of-overt (X , sX) (Y , sY) f sf overt-X (P , open-P) =
 ⇔-affirmable (Ǝₚ x ꞉ X , P (f x)) (Ǝₚ y ꞉ Y , P y) (p₁ , p₂) †
  where
   p₁ : ((Ǝₚ x ꞉ X , P (f x)) ⇒ (Ǝₚ y ꞉ Y , P y)) holds
   p₁ = λ pX → ∥∥-rec (holds-is-prop (Ǝₚ y ꞉ Y , P y)) (λ (x , Pxf) → ∣ f x , Pxf  ∣) pX

   exists-preimage-of-y : (y : Y) → ((Ǝₚ x ꞉ X , ((f x ＝ y) , sY)) holds)
   exists-preimage-of-y y =
    surjection-induction f sf (λ y → ((Ǝₚ x ꞉ X , ((f x ＝ y) , sY)) holds))
                                                 (λ y → holds-is-prop (Ǝₚ x ꞉ X , ((f x ＝ y) , sY)))
                                                 (λ x → ∣ x , refl  ∣)
                                                  y

   p₂ : ((Ǝₚ y ꞉ Y , P y) ⇒ Ǝₚ x ꞉ X , P (f x)) holds
   p₂ = λ pY → ∥∥-rec (holds-is-prop (Ǝₚ x ꞉ X , P (f x)))
                          (λ (y , Py) →
                           ∥∥-rec (holds-is-prop (Ǝₚ x ꞉ X , P (f x)))
                            (λ (x , x-eq-fy) → ∣ x ,  transport (λ y' → P y' holds) (x-eq-fy ⁻¹) Py ∣)
                            (exists-preimage-of-y y))
                           pY
                           
   † : is-affirmable (Ǝₚ x ꞉ X , P (f x)) holds
   † = overt-X ((P ∘ f) , (open-P ∘ f))

\end{code}
