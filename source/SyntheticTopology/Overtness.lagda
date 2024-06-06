---
title:        Overtness in Synthetic Topology
author:       Martin Trucchi
date-started: 2024-05-28
dates-modified: [2024-06-06]
---

We implement here the notion of overtness in Synthetic Topology defined here :
TODO, and prove some lemmas.

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

Overtness is a dual notion of compactness.
A set is `overt` if the proposition `∃ x , P x` is `open` whenever `P` is
`open`.

\begin{code}

module _ (𝒳 : hSet 𝓤) where
 private
  X = underlying-set 𝒳

 is-overt : Ω (𝓤 ⁺ ⊔ 𝓥)
 is-overt = Ɐ (P , open-P) ꞉ 𝓞 𝒳 , is-open-proposition (Ǝₚ x ꞉ X , P x)

\end{code}

The type `𝟙` is always overt, regardless of the Sierpinski object.

\begin{code}

𝟙-is-overt : is-overt (𝟙 , 𝟙-is-set) holds
𝟙-is-overt (P , open-P) = ⇔-open (P ⋆) (Ǝₚ x ꞉ 𝟙 , P x) (p₁ , p₂) (open-P ⋆)
 where
  p₁ : (P ⋆ ⇒ Ǝₚ x ꞉ 𝟙 , P x) holds
  p₁ P-star = ∣ ⋆ , P-star ∣

  p₂ : (Ǝₚ x ꞉ 𝟙 , P x ⇒ P ⋆) holds
  p₂ exists-x = ∥∥-rec (holds-is-prop (P ⋆)) (λ (x , Px) → Px) exists-x

\end{code}

We prove here, similar to `image-of-compact`, that image of `overt` sets are
`overt`.

\begin{code}

module _ (𝒳 𝒴 : hSet 𝓤) where
 private
  X = underlying-set 𝒳
  Y = underlying-set 𝒴
  set-Y = pr₂ 𝒴

 image-of-overt : (f : X → Y)
                → is-surjection f
                → is-overt 𝒳 holds
                → is-overt 𝒴 holds

 image-of-overt f sf overt-X (P , open-P) =
  ⇔-open preimage-exists image-exists (p₁ , p₂) †
   where
    preimage-exists : Ω 𝓤
    preimage-exists = Ǝₚ x ꞉ X , P (f x)

    image-exists : Ω 𝓤
    image-exists = Ǝₚ y ꞉ Y , P y

    p₁ : (preimage-exists ⇒ image-exists) holds
    p₁ Px = ∥∥-rec (holds-is-prop image-exists)
                   (λ (x , Pxf) → ∣ f x , Pxf  ∣)
                   Px

    exists-preimage-of-y : (y : Y) → (Ǝₚ x ꞉ X , ((f x ＝ y) , set-Y)) holds
    exists-preimage-of-y y =
     surjection-induction f
                          sf
                          (λ y → ((Ǝₚ x ꞉ X , ((f x ＝ y) , set-Y)) holds))
                          (λ y → holds-is-prop
                                  (Ǝₚ x ꞉ X , ((f x ＝ y) , set-Y)))
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
