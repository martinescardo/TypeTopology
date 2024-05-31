---
title:        Compactness in Synthetic Topology
author:       Martin Trucchi
date-started: 2024-05-28
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import SyntheticTopology.SierpinskiObject
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.SubtypeClassifier

module SyntheticTopology.Compactness
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

We here start to investigate a notion of compactness.

A type `X` is called compact if its universal quantification on intrinsically
open predicates is affirmable.

\begin{code}

is-compact : hSet 𝓤 → Ω ((𝓤 ⁺) ⊔ 𝓥)
is-compact (X , sX) =
 Ɐ (P , open-P) ꞉ 𝓞 (X , sX) , is-open-proposition (Ɐ x ꞉ X , (P x))

\end{code}

The type `𝟙` is compact i.e. the empty product is compact, regardless of the
Sierpinski Object. 

\begin{code}

𝟙-is-compact : is-compact (𝟙 , 𝟙-is-set) holds
𝟙-is-compact (P , open-P) =
 ⇔-affirmable (P ⋆) (Ɐ x ꞉ 𝟙 , P x) p (open-P ⋆)
  where
   p : (P ⋆ ⇔ (Ɐ x ꞉ 𝟙 , P x)) holds
   p = (λ pstar  x → pstar) , (λ f → f ⋆)

\end{code}

Binary products of compact types are compact. The proof of the binary product
being a set is given by ×-is-set.

\begin{code}

×-is-compact : ((X , sX) (Y , sY) : hSet 𝓤)
               → is-compact (X , sX) holds
               → is-compact (Y , sY) holds
               → is-compact((X × Y) , (×-is-set sX sY)) holds
               
×-is-compact (X , sX) (Y , sY) kX kY (P , open-P) =
 ⇔-affirmable chained-forall
               tuple-forall
               (p₁ , p₂)
               †
  where
   tuple-forall : Ω 𝓤
   tuple-forall = (Ɐ z ꞉ (X × Y) , P z)
   
   chained-forall : Ω 𝓤
   chained-forall = (Ɐ x ꞉ X , (Ɐ y ꞉ Y , P (x , y)))
   
   p₁ : (chained-forall ⇒ tuple-forall) holds
   p₁ =  (λ Qxy z → Qxy (pr₁ z) (pr₂ z))

   p₂ : (tuple-forall ⇒ chained-forall) holds
   p₂ = (λ Qz x' y' → Qz (x' , y'))

   prop-y : X → Ω 𝓤
   prop-y x = Ɐ y ꞉ Y , P (x , y)

   prop-y-open : (x : X) → is-open-proposition (prop-y x) holds 
   prop-y-open x = kY ((λ y → P (x , y)) , λ y → open-P (x , y))

   † : is-open-proposition chained-forall  holds
   † = kX ((λ x → prop-y x) , λ x → prop-y-open x)

\end{code}

Images of compact types are compact. We require the function to be surjective.
We could also try to prove that this works for any f, and prove that (image f)
is compact.

\begin{code}

image-of-compact : ((X , sX) (Y , sY) : hSet 𝓤)
                   → (f : X → Y)
                   → is-surjection f
                   → is-compact (X , sX) holds
                   → is-compact (Y , sY) holds
image-of-compact (X , sX) (Y , sY) f sf kX (P , open-P) =
 ⇔-affirmable pre-image-forall image-forall (p₁ , p₂) †
  where
   pre-image-forall : Ω 𝓤
   pre-image-forall = (Ɐ x ꞉ X , P (f x))
   
   image-forall : Ω 𝓤
   image-forall = (Ɐ y ꞉ Y , P y)
   
   p₁ : (pre-image-forall ⇒ image-forall) holds
   p₁ pX y = surjection-induction f
                                  sf
                                  (_holds ∘ P)
                                  (λ y → holds-is-prop (P y))
                                  pX
                                  y
   
   p₂ : (image-forall ⇒ pre-image-forall) holds
   p₂ = λ pY x → pY (f x)

   † : is-open-proposition pre-image-forall holds
   † = kX ((P ∘ f) , (open-P ∘ f))

\end{code}

