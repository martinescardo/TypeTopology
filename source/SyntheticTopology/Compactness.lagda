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
open import UF.Powerset
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-Properties
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
open import SyntheticTopology.SetCombinators 𝓤 fe pe pt

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open Sierpinski-notations fe pe pt 𝕊

\end{code}

We here start to investigate a notion of compactness defined in [1] and [2].

A type `X` is called `compact` if its universal quantification on
`intrinsically-open` predicates is an open proposition.

\begin{code}

module _ (𝒳 : hSet 𝓤) where
 private
  X = underlying-set 𝒳

 is-compact : Ω (𝓤 ⁺ ⊔ 𝓥)
 is-compact =
  Ɐ (P , open-P) ꞉ 𝓞 𝒳 , is-open-proposition (Ɐ x ꞉ X , x ∈ₚ P)

\end{code}

The type `𝟙` is compact i.e. the empty product is compact, regardless of the
Sierpinski Object.

\begin{code}

𝟙-is-compact : is-compact 𝟙ₛ holds
𝟙-is-compact (P , open-P) =
 ⇔-open (⋆ ∈ₚ P) (Ɐ x ꞉ 𝟙 , x ∈ₚ P) eq (open-P ⋆)
  where
   eq : (⋆ ∈ₚ P ⇔ (Ɐ x ꞉ 𝟙 , x ∈ₚ P)) holds
   eq = (λ pstar  x → pstar) , (λ f → f ⋆)

\end{code}

Binary products of compact types are compact.

\begin{code}

module _ (𝒳 𝒴 : hSet 𝓤) where
 private
  X = underlying-set 𝒳
  Y = underlying-set 𝒴

 ×-is-compact : is-compact 𝒳 holds
              → is-compact 𝒴 holds
              → is-compact (𝒳 ×ₛ 𝒴)  holds

 ×-is-compact compact-X compact-Y (P , open-P) =
  ⇔-open chained-forall
         tuple-forall
         (p₁ , p₂)
         †
   where
    tuple-forall : Ω 𝓤
    tuple-forall = Ɐ z ꞉ (X × Y) , z ∈ₚ P

    chained-forall : Ω 𝓤
    chained-forall = Ɐ x ꞉ X , (Ɐ y ꞉ Y , (x , y) ∈ₚ P)

    p₁ : (chained-forall ⇒ tuple-forall) holds
    p₁ = λ Qxy z → Qxy (pr₁ z) (pr₂ z)

    p₂ : (tuple-forall ⇒ chained-forall) holds
    p₂ = λ Qz x' y' → Qz (x' , y')

    prop-y : 𝓟 X
    prop-y x = Ɐ y ꞉ Y , (x , y) ∈ₚ P

    prop-y-open : (x : X) → is-open-proposition (prop-y x) holds
    prop-y-open x = compact-Y ((λ y → (x , y) ∈ₚ P) , λ y → open-P (x , y))

    † : is-open-proposition chained-forall holds
    † = compact-X ((λ x → prop-y x) , prop-y-open)

\end{code}

Images of compact types by surjective functions are compact.

\begin{code}

 image-of-compact : (f : X → Y)
                  → is-surjection f
                  → is-compact 𝒳 holds
                  → is-compact 𝒴 holds
 image-of-compact f sf compact-X (P , open-P) =
  ⇔-open pre-image-forall image-forall (p₁ , p₂) †
   where
    pre-image-forall : Ω 𝓤
    pre-image-forall = Ɐ x ꞉ X , (f x) ∈ₚ P

    image-forall : Ω 𝓤
    image-forall = Ɐ y ꞉ Y , y ∈ₚ P

    p₁ : (pre-image-forall ⇒ image-forall) holds
    p₁ pX y = surjection-induction f
                                   sf
                                   (_holds ∘ P)
                                   (λ y → holds-is-prop (P y))
                                   pX
                                   y

    p₂ : (image-forall ⇒ pre-image-forall) holds
    p₂ pY x = pY (f x)

    † : is-open-proposition pre-image-forall holds
    † = compact-X (P ∘ f , open-P ∘ f)

\end{code}

This also works for any function, in which case we prove that `image f` is
compact.

We have to get out of the module defining `𝒳` and `𝒴` in order to apply the
previous lemma.

\begin{code}

image-of-compact' : ((X , sX) : hSet 𝓤)
                  → ((Y , sY) : hSet 𝓤)
                  → (f : X → Y)
                  → is-compact (X , sX) holds
                  → is-compact (imageₛ (X , sX) (Y , sY) f) holds

image-of-compact' (X , sX) (Y , sY) f compact-X =
 image-of-compact (X , sX)
                  (imageₛ (X , sX) (Y , sY) f)
                  (corestriction f)
                  (corestrictions-are-surjections f)
                  compact-X

\end{code}

\section{References}

- [1]: Davorin Lesňik. *Synthetic Topology and Constructive Metric Spaces*.

  PhD Thesis, 2010

  https://doi.org/10.48550/arXiv.2104.10399

- [2]: Martín Escardó. *Topology via higher-order intuitionistic logic*

  Unpublished notes, Pittsburgh, 2004

  https://www.cs.bham.ac.uk/~mhe/papers/pittsburgh.pdf
