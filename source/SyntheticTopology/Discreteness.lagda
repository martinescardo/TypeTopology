---
title:          Discreteness in Synthetic Topology
author:         Martin Trucchi
date-started:   2024-05-28
dates-modified: [2024-06-07]
---

We here implement the notion of discreteness in Synthetic Topology defined
in [1] and [2], and then prove two lemmas.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Powerset
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
open import SyntheticTopology.SetCombinators 𝓤 fe pe pt
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
  set-X = pr₂ 𝒳
  open Equality set-X

 is-discrete : Ω (𝓤 ⊔ 𝓥)
 is-discrete = is-intrinsically-open (𝒳 ×ₛ 𝒳) (λ (x , y) → x ＝ₚ y)

\end{code}

We prove here that `𝟙` is discrete as long as the true truth value lies in the
Sierpinski object's image.

\begin{code}

𝟙-is-discrete : contains-top holds
              → is-discrete 𝟙ₛ holds

𝟙-is-discrete ct (⋆ , ⋆) =
 ⇔-open ⊤ (⋆ ＝ₚ ⋆) (p₁ , p₂) ct
  where
   open Equality 𝟙ₛ-is-set

   p₁ : (⊤ ⇒ (⋆ ＝ₚ ⋆)) holds
   p₁ = λ _ → refl

   p₂ : ((⋆ ＝ₚ ⋆) ⇒ ⊤) holds
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
    open Equality (pr₂ (Πₛ 𝒳 Y))

    extensional-eq : Ω 𝓤
    extensional-eq = Ɐ x ꞉ X , ((y₁ x ＝ y₂ x) , pr₂ (Y x))

    global-eq : Ω 𝓤
    global-eq = y₁ ＝ₚ y₂

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

\section{References}

- [1]: Davorin Lesňik. *Synthetic Topology and Constructive Metric Spaces*.

  PhD Thesis, 2010

  https://doi.org/10.48550/arXiv.2104.10399

- [2]: Martín Escardó. *Topology via higher-order intuitionistic logic*

  Unpublished notes, Pittsburgh, 2004

  https://www.cs.bham.ac.uk/~mhe/papers/pittsburgh.pdf
