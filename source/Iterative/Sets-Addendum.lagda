Martin Escardo & Tom de Jong, July 2023.

Some constructions with iterative sets.

 * The type of iterative sets is algebraically injective.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Univalence

module Iterative.Sets-Addendum
        (ua : Univalence)
        (𝓤 : Universe)
       where

open import Iterative.Multisets 𝓤
open import Iterative.Multisets-Addendum ua 𝓤
open import Iterative.Sets ua 𝓤
open import Taboos.Decomposability ua
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.UA-FunExt

private
 𝓤⁺ : Universe
 𝓤⁺ = 𝓤 ⁺

 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

𝟘ⱽ : 𝕍
𝟘ⱽ = 𝟘ᴹ , 𝟘ᴹ-is-iset

𝟙ⱽ : 𝕍
𝟙ⱽ = 𝟙ᴹ , 𝟙ᴹ-is-iset

𝟘ⱽ-is-not-𝟙ⱽ : 𝟘ⱽ ≠ 𝟙ⱽ
𝟘ⱽ-is-not-𝟙ⱽ p = 𝟘ᴹ-is-not-𝟙ᴹ (ap underlying-mset p)

open import InjectiveTypes.Blackboard fe'

module _ (pt : propositional-truncations-exist)
         (sr : Set-Replacement pt)
       where

 𝕍-is-ainjective : ainjective-type 𝕍 𝓤 𝓤
 𝕍-is-ainjective = retract-of-ainjective 𝕍 𝕄 𝕄-is-ainjective 𝕍-is-retract-of-𝕄
  where
   open unions-of-iterative-sets pt sr

\end{code}

It follows that 𝕍 has no non-trivial decidable properties unless weak
excluded middle holds.

\begin{code}

 decomposition-of-𝕍-gives-WEM : decomposition 𝕍 → WEM 𝓤
 decomposition-of-𝕍-gives-WEM =
  decomposition-of-ainjective-type-gives-WEM
   𝕍
   𝕍-is-ainjective

\end{code}
