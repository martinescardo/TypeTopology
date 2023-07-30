Martin Escardo July 2023.

Some constructions with iterative sets.

 * The type of iterative sets is algebraicly injective.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Univalence

module Iterative.Sets-Addendum
        (𝓤 : Universe)
        (ua : Univalence)
       where

open import Iterative.Multisets 𝓤
open import Iterative.Multisets-Addendum 𝓤 ua
open import Iterative.Sets 𝓤 ua
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Miscelanea
open import UF.PropTrunc
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.Univalence
open import W.Type
open import W.Properties (𝓤 ̇) id

private
 𝓤⁺ : Universe
 𝓤⁺ = 𝓤 ⁺

 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import InjectiveTypes.Blackboard fe'

𝕍-is-ainjective : (pt : propositional-truncations-exist)
                → Set-Replacement pt
                → ainjective-type 𝕍 𝓤 𝓤
𝕍-is-ainjective pt sr = retract-of-ainjective 𝕍 𝕄 𝕄-is-ainjective 𝕍-is-retract-of-𝕄
 where
  open unions-of-iterative-sets pt sr

\end{code}
