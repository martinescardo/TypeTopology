---
title:          Overtness in Synthetic Topology
author:         Martin Trucchi
date-started:   2024-05-28
dates-modified: [2024-06-06]
---

We implement here the notion of overtness in Synthetic Topology defined here :
[1] and [2]. We then foramlize some lemmas.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import SyntheticTopology.SierpinskiObject
open import UF.FunExt
open import UF.Logic
open import UF.Powerset
open import UF.PropTrunc
open import UF.Sets
open import UF.Subsingletons
open import UF.SubtypeClassifier

module SyntheticTopology.Overtness
        (𝓤  𝓥 : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (𝕊 : Generalized-Sierpinski-Object fe pe pt 𝓤 𝓥)
        where

open import SyntheticTopology.SetCombinators 𝓤 fe pe pt
open import UF.ImageAndSurjection pt

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open Sierpinski-notations fe pe pt 𝕊

\end{code}

Overtness

Overtness is a dual notion of compactness.
A set is `overt` if the proposition `∃ x , x ∈ₚ P` is `open` whenever `P` is
`open`.

\begin{code}

module _ (𝒳 : hSet 𝓤) where
 private
  X = underlying-set 𝒳

 is-overt : Ω (𝓤 ⁺ ⊔ 𝓥)
 is-overt = Ɐ (P , open-P) ꞉ 𝓞 𝒳 , is-open-proposition (Ǝₚ x ꞉ X , x ∈ₚ P)

\end{code}

The type `𝟙` is always overt, regardless of the Sierpinski object.

\begin{code}

𝟙-is-overt : is-overt 𝟙ₛ holds
𝟙-is-overt (P , open-P) =
 ⇔-open (⋆ ∈ₚ P) (Ǝₚ x ꞉ 𝟙 , x ∈ₚ P) (p₁ , p₂) (open-P ⋆)
 where
  p₁ : (⋆ ∈ₚ P ⇒ Ǝₚ x ꞉ 𝟙 , x ∈ₚ P) holds
  p₁ P-star = ∣ ⋆ , P-star ∣

  p₂ : (Ǝₚ x ꞉ 𝟙 , x ∈ₚ P ⇒ ⋆ ∈ₚ P) holds
  p₂ exists-x = ∥∥-rec (holds-is-prop (⋆ ∈ₚ P)) (λ (x , Px) → Px) exists-x

\end{code}

We prove here, similar to `image-of-compact`, that image of `overt` sets are
`overt`.

\begin{code}

module _ (𝒳 𝒴 : hSet 𝓤) where
 private
  X = underlying-set 𝒳
  Y = underlying-set 𝒴
  set-Y = pr₂ 𝒴
  open Equality set-Y

 image-of-overt : (f : X → Y)
                → is-surjection f
                → is-overt 𝒳 holds
                → is-overt 𝒴 holds

 image-of-overt f sf overt-X (P , open-P) =
  ⇔-open preimage-exists image-exists (p₁ , p₂) †
   where
    preimage-exists : Ω 𝓤
    preimage-exists = Ǝₚ x ꞉ X , (f x) ∈ₚ P

    image-exists : Ω 𝓤
    image-exists = Ǝₚ y ꞉ Y , y ∈ₚ P

    p₁ : (preimage-exists ⇒ image-exists) holds
    p₁ Px = ∥∥-rec (holds-is-prop image-exists)
                   (λ (x , Pxf) → ∣ f x , Pxf  ∣)
                   Px

    exists-preimage-of-y : (y : Y) → (Ǝₚ x ꞉ X , (f x ＝ₚ y)) holds
    exists-preimage-of-y y =
     surjection-induction f
                          sf
                          (λ y → ((Ǝₚ x ꞉ X , (f x ＝ₚ y)) holds))
                          (λ y → holds-is-prop
                                  (Ǝₚ x ꞉ X , (f x ＝ₚ y)))
                          (λ x → ∣ x , refl  ∣)
                          y

    p₂ : (image-exists ⇒ preimage-exists) holds
    p₂ Py-prop = ∥∥-rec (holds-is-prop preimage-exists)
                        (λ (y , Py) → ∥∥-rec (holds-is-prop preimage-exists)
                                             (λ (x , x-eq-fy) →
                                              ∣ x , transport (_holds ∘ P)
                                                              (x-eq-fy ⁻¹)
                                                              Py
                                              ∣)
                                             (exists-preimage-of-y y))
                        Py-prop

    † : is-open-proposition preimage-exists holds
    † = overt-X (P ∘ f , open-P ∘ f)

\end{code}

As for `image-of-compact'`, there is a version for any function `f : X → Y`, in
which case `image f` is overt as a set.

We have to get out of the anonymous module to access the previous version of
`image-of-overt`.

\begin{code}

image-of-overt' : ((X , sX) : hSet 𝓤)
                → ((Y , sY) : hSet 𝓤)
                → (f : X → Y)
                → is-overt (X , sX) holds
                → is-overt (imageₛ (X , sX) (Y , sY) f) holds

image-of-overt' (X , sX) (Y , sY) f overt-X =
 image-of-overt (X , sX)
                  (imageₛ (X , sX) (Y , sY) f)
                  (corestriction f)
                  (corestrictions-are-surjections f)
                  overt-X

\end{code}

\section{References}

- [1]: Davorin Lesňik. *Synthetic Topology and Constructive Metric Spaces*.

  PhD Thesis, 2010

  https://doi.org/10.48550/arXiv.2104.10399

- [2]: Martín Escardó. *Topology via higher-order intuitionistic logic*

  Unpublished notes, Pittsburgh, 2004

  https://www.cs.bham.ac.uk/~mhe/papers/pittsburgh.pdf
