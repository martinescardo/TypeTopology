Ian Ray, 4th Febuary 2024.

We develop some results that relate size and truncatedness from a paper by Dan
Chirstensen (see https://browse.arxiv.org/abs/2109.06670).

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.SizeAndTruncation where

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.Hedberg
open import UF.KrausLemma
open import UF.PropIndexedPiSigma
open import UF.PropTrunc
open import UF.Retracts
open import UF.Size
open import UF.Section-Embedding
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.Univalence
open import UF.UniverseEmbedding
open import Naturals.Order
open import Naturals.Properties

module _ (fe : FunExt) (fe' : Fun-Ext) where

 open import UF.H-Levels fe fe'

 module _ (𝓥 : Universe) (te : H-level-truncations-exist) where

\end{code}

We begin by giving some definitions that Dan uses in his paper. We will use
𝓥 as our point of reference for 'smallness'.

\begin{code}

  _is_locally-small : (X : 𝓤 ̇) → (n : ℕ) → {!!} ̇
  X is zero locally-small = X is 𝓥 small
  X is (succ n) locally-small = (x x' : X) → (x ＝ x') is n locally-small

\end{code}

We will now begin proving some of the results of the paper. We will attempt to
avoid any unnecesay use of propositional resizing. Theorem numbers will be
provided for easy reference.

WARNING: Be aware that our notions are 'off by two' which results from our
choice of H-levels.

Proposition 2.2.

\begin{code}

  open H-level-truncations-exist te
  open k-connectedness te

  Prop-2-2 : {A : 𝓤 ̇} {X : 𝓦 ̇} (f : A → X)
           → (n : ℕ)
           → 1 ≤ℕ n
           → map f is (pred n) connected
           → A is 𝓥 small
           → X is (succ n) locally-small
           → X is 𝓥 small
  Prop-2-2 = {!!}

\end{code}

