---
title:  Compactness in Synthetic Topology
author: Martin Trucchi
---

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import SyntheticTopology.SierpinskiObject 

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


We here start to investigate some notions of compactness.

A type `X` is called compact if its universal quantification on intrinsically
open predicates is affirmable.

\begin{code}

is-compact : hSet 𝓤 → Ω ((𝓤 ⁺) ⊔ 𝓥)
is-compact (X , sX) =
   Ɐ (P , open-P) ꞉ 𝓞 (X , sX) ,  is-affirmable (Ɐ x ꞉ X , (P x))

\end{code}

The type `𝟙` is compact i.e. the empty product is compact.

\begin{code}

𝟙-is-compact : (𝟙-is-set : is-set 𝟙) → is-compact (𝟙 , 𝟙-is-set) holds
𝟙-is-compact 𝟙-is-set (P , open-P) = ⇔-affirmable (P ⋆) (Ɐ x ꞉ 𝟙 , P x) p (open-P ⋆)
 where
  p : (P ⋆ ⇔ (Ɐ x ꞉ 𝟙 , P x)) holds
  p = (λ pstar  x → pstar) , (λ f → f ⋆)

\end{code}

Binary products of compact types are compact.

\begin{code}

×-is-compact : {(X , sX) (Y , sY) : hSet 𝓤 }
               → is-compact (X , sX) holds
               → is-compact (Y , sY) holds
               → is-compact((X × Y) , (×-is-set sX sY)) holds
×-is-compact {X , sX} {Y , sY} kX kY (P , open-P) = ⇔-affirmable (Ɐ x ꞉ X , (Ɐ y ꞉ Y , P (x , y))) (Ɐ z ꞉ (X × Y) , P z) p †
  where
   p : ((Ɐ x ꞉ X , (Ɐ y ꞉ Y , P (x , y))) ⇔ (Ɐ z ꞉ (X × Y) , P z) ) holds
   p =  (λ Qxy z → Qxy (pr₁ z) (pr₂ z)) , (λ Qz x' y' → Qz (x' , y') )

   † : is-affirmable (Ɐ x ꞉ X , (Ɐ y ꞉ Y ,  P (x , y)))  holds
   † = kX ((λ x → Ɐ y ꞉ Y , P (x , y)) , (λ x → kY ((λ y → P (x , y)) , ( λ y → open-P (x , y) ))))

\end{code}

Images of compact types are compact.

\begin{code}

image-of-compact : {(X , sX) (Y , sY) : hSet 𝓤}
                   → (f : X → Y)
                   → is-surjection f
                   → is-compact (X , sX) holds
                   → is-compact (Y , sY) holds
image-of-compact {X , sX} {Y , sY} f surf kX (P , open-P) = ⇔-affirmable (Ɐ x ꞉ X , P (f x)) (Ɐ y ꞉ Y , P y) p †
  where
   p : ((Ɐ x ꞉ X , P (f x)) ⇔ (Ɐ y ꞉ Y , P y)) holds
   p = (λ pX y → surjection-induction f surf (_holds ∘ P) (λ y → holds-is-prop (P y)) pX y)
     , (λ pY x → pY (f x))

   † : is-affirmable (Ɐ x ꞉ X , P (f x)) holds
   † = kX ((P ∘ f) , (open-P ∘ f))

\end{code}
