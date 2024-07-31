---
title:         Density in Synthetic Topology
author:        Martin Trucchi
date-started : 2024-05-28
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.Powerset
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import SyntheticTopology.SierpinskiObject

module SyntheticTopology.Density
        (𝓤  𝓥 : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (𝕊 : Generalized-Sierpinski-Object fe pe pt 𝓤 𝓥)
        (𝒳 : hSet 𝓤)
        where

open import SyntheticTopology.Compactness 𝓤 𝓥 fe pe pt 𝕊
open import SyntheticTopology.Overtness 𝓤 𝓥 fe pe pt 𝕊
open import SyntheticTopology.SubObjects 𝓤 𝓥 fe pe pt 𝕊
open import UF.ImageAndSurjection pt
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open Sierpinski-notations fe pe pt 𝕊

\end{code}

Density in synthetic topology. The definition comes from [1].

A subset `D` of a set `X` is dense if `D` intersects every inhabited open
subset of `X`. 

The whole module is parametrized by a set `𝒳`.

`is-dense 𝒳 D` should be read "D is dense in X".

\begin{code}
private
 X = underlying-set 𝒳

is-dense : (D : 𝓟 X) → Ω (𝓤 ⁺ ⊔ 𝓥)
is-dense D =
 Ɐ (U , open-U) ꞉ 𝓞 𝒳 ,
  (Ǝₚ x ꞉ X , x ∈ₚ U) ⇒
   (Ǝₚ x ꞉ X , (x ∈ₚ (D ∩ U)))

\end{code}

We now prove two lemmas, stating respectively that a set is dense in itself
and that a set containing a subovert dense subset is itself overt.

\begin{code}

self-is-dense-in-self : is-dense full holds
self-is-dense-in-self (P , open-P) inhabited-P =
 ∥∥-rec (holds-is-prop (Ǝₚ x' ꞉ X , (x' ∈ₚ (full ∩ P)))) † inhabited-P
  where
   † : Σ x ꞉ X , x ∈ₚ P holds → (Ǝₚ x' ꞉ X , (x' ∈ₚ (full ∩ P))) holds
   † (x , Px) = ∣ x , ⊤-holds , Px  ∣

\end{code}

\section{References}

- [1]: Davorin Lesňik. *Synthetic Topology and Constructive Metric Spaces*.

  PhD Thesis, 2010

  https://doi.org/10.48550/arXiv.2104.10399
