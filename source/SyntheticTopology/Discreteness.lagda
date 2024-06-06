---
title:        Discreteness in Synthetic Topology
author:       Martin Trucchi
date-started: 2024-05-28
dates-modified: [2024-06-06]
---

We here implement the notion of discreteness in Synthetic Topology defined
in TODO and prove two lemmas.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.DiscreteAndSeparated hiding (is-discrete ; 𝟙-is-discrete)
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
open import SyntheticTopology.SierpinskiAxioms 𝓤 𝓥 fe pe pt 𝕊
open import UF.ImageAndSurjection pt
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open Sierpinski-notations fe pe pt 𝕊

\end{code}

Discrete sets.

A set `𝒳` is `discrete` if its equality map `λ (x , y) → x ＝ y` is
`intrinsically-open` in the product set `𝒳 × 𝒳`.

\begin{code}

module _ (𝒳 : hSet 𝓤) where
 private
  X = underlying-set 𝒳

 is-discrete : Ω (𝓤 ⊔ 𝓥)
 is-discrete =
  is-intrinsically-open (𝒳 ×ₛ 𝒳)
                        λ ((x , y) : X × X) → (x ＝ y) , pr₂ 𝒳

\end{code}

We prove here that `𝟙` is discrete as long as the true truth value lies in the
Sierpinski object's image.

\begin{code}

𝟙-is-discrete : contains-top holds
              → is-discrete (𝟙 , 𝟙-is-set) holds

𝟙-is-discrete ct (⋆ , ⋆) =
 ⇔-open ⊤ ((⋆ ＝ ⋆) , 𝟙-is-set) (p₁ , p₂) ct
  where
   p₁ : (⊤ ⇒ (⋆ ＝ ⋆) , 𝟙-is-set) holds
   p₁ = λ _ → refl

   p₂ : (((⋆ ＝ ⋆) , 𝟙-is-set) ⇒ ⊤) holds
   p₂ = λ _ → ⊤-holds

\end{code}

Compact indexed product of discrete set is itself discrete.

\begin{code}

module _ (𝒳 : hSet 𝓤) where
 private
  X = underlying-set 𝒳

 compact-Π-discrete : (Y : X → hSet 𝓤)
                    → is-compact 𝒳 holds
                    → ((x : X) → is-discrete (Y x) holds)
                    → is-discrete (Πₛ 𝒳 Y) holds

 compact-Π-discrete Y compact-X discrete-Y (y₁ , y₂) =
  ⇔-open extensional-eq global-eq (p₁ , p₂) †
   where
    extensional-eq : Ω 𝓤
    extensional-eq = Ɐ x ꞉ X , ((y₁ x ＝ y₂ x) , pr₂ (Y x))

    global-eq : Ω 𝓤
    global-eq = (y₁ ＝ y₂) , pr₂ (Πₛ 𝒳 Y)

    p₁ : (extensional-eq ⇒ global-eq) holds
    p₁ = dfunext fe

    p₂ : (global-eq ⇒ extensional-eq) holds
    p₂ y₁-eq-y₂ = transport (λ - → (x : X) → ((y₁ x) ＝ ( - x)))
                            y₁-eq-y₂
                            λ _ → refl

    † : is-open-proposition extensional-eq holds
    † = compact-X ((λ x → (y₁ x ＝ y₂ x) , pr₂ (Y x)) ,
                  λ x → discrete-Y x (y₁ x , y₂ x))

\end{code}
