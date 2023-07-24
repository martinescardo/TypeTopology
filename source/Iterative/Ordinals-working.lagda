Martin Escardo & Tom de Jong, June 2023.

More about iterative ordinals and their relation to iterative (multi)sets.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan
open import UF.Univalence

module Iterative.Ordinals-working
        (𝓤 : Universe)
        (ua : Univalence)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 𝓤⁺ : Universe
 𝓤⁺ = 𝓤 ⁺

 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import Iterative.Multisets 𝓤
open import Iterative.Sets 𝓤 ua
open import MLTT.W
open import Ordinals.Equivalence
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type hiding (Ord)
open import Ordinals.Underlying
open import Ordinals.WellOrderTransport
open import UF.Equiv-FunExt
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PairFun
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\begin{code}

𝕍-recursion : (P : 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) → (X → P) → P)
            → 𝕍 → P
𝕍-recursion P RH = 𝕍-induction
                    (λ _ → P)
                    (λ X _ _ → RH X)


rank : 𝕍 → 𝕆
rank = 𝕍-induction (λ _ → 𝕆) {!!}
 where
  f : (X : 𝓤 ̇) (ϕ : X → 𝕍) → is-embedding ϕ
    → (X → 𝕆) → 𝕆
  f = {!!}

\end{code}
