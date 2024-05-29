---
title:                  Discreteness in Synthetic Topology
author:             Martin Trucchi
date-started:  2024-05-28
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import SyntheticTopology.SierpinskiObject 

module SyntheticTopology.Discreteness
        (𝓤 𝓥 : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (𝕊 : Generalized-Sierpinski-Object fe pe pt 𝓤 𝓥)
        where

open import SyntheticTopology.Compactness 𝓤 𝓥 fe pe pt 𝕊
open import SyntheticTopology.Dominance 𝓤 𝓥 fe pe pt 𝕊
open import UF.ImageAndSurjection pt
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open Sierpinski-notations fe pe pt 𝕊

\end{code}

Discrete spaces.

Being discrete means having affirmable equality.
The proof of the product to be a set is given be ×-is-set.

\begin{code}

is-discrete : ((X , sX) : hSet 𝓤) → Ω (𝓤 ⊔ 𝓥)
is-discrete (X , sX) =
 is-intrinsically-open ((X × X) , (×-is-set sX sX)) (λ ((x , y) : X × X) → ((x ＝ y) , sX))


\end{code}

We prove here that 𝟙 is discrete as long as the true truth value lies in the
Sierpinski object's image.
As in compactness, having a proof that 𝟙 is actually a set would be better.

\begin{code}

𝟙-is-discrete : contains-top holds
                    → (𝟙-is-set : is-set 𝟙)
                    → is-discrete (𝟙 , 𝟙-is-set) holds

𝟙-is-discrete ct 𝟙-is-set (⋆ , ⋆) =
 ⇔-affirmable ⊤ ((⋆ ＝ ⋆) , 𝟙-is-set) (p₁ , p₂) ct
  where
   p₁ : (⊤ ⇒ (⋆ ＝ ⋆) , 𝟙-is-set) holds
   p₁ = λ _ → refl
   
   p₂ : (((⋆ ＝ ⋆) , 𝟙-is-set) ⇒ ⊤) holds
   p₂ = λ _ → ⊤-holds

\end{code}

Compact indexed product of discrete set is itself discrete.
The proof requires functional extensionality and uses Π-is-set to construct the proof
that the Π type is a set.


\begin{code}

compact-Π-discrete : ((K , sK) : hSet 𝓤) → (X : K → hSet 𝓤)
                        → is-compact (K , sK) holds
                        → ((k : K) → is-discrete (X k) holds)
                        → is-discrete
                              (Π (λ k → (underlying-set (X k))) , (Π-is-set fe (λ k → (pr₂ (X k))))) holds
compact-Π-discrete (K , sK) X kK dX (x₁ , x₂) =
 ⇔-affirmable extensional-eq global-eq (p₁ , p₂) †
  where
   extensional-eq : Ω 𝓤
   extensional-eq = (Ɐ k ꞉ K , ((x₁ k ＝ x₂ k) , pr₂ (X k)))

   global-eq : Ω 𝓤
   global-eq = ((x₁ ＝ x₂) , Π-is-set fe (λ k → pr₂ (X k)))
   
   p₁ : (extensional-eq ⇒ global-eq) holds
   p₁ = dfunext fe
   
   p₂ : (global-eq ⇒ extensional-eq) holds
   p₂ = λ x₁-eq-x₂ → transport (λ - → ((k : K) → ((x₁ k)  ＝ ( - k) ))) x₁-eq-x₂ (λ _ → refl)

   † : is-affirmable extensional-eq holds
   † = kK ((λ k → (x₁ k ＝ x₂ k) , pr₂ (X k)) , (λ k → dX k (x₁ k , x₂ k)))

\end{code}
