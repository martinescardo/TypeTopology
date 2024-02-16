Ian Ray, 4th Febuary 2024.

We develop some results that relate size and truncatedness from a paper by Dan
Chirstensen (see https://browse.arxiv.org/abs/2109.06670).

\begin{code}

{-# OPTIONS --safe --without-K #-}

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
open import Naturals.Addition
open import Naturals.Order
open import Naturals.Properties

module UF.SizeAndTruncation (fe : FunExt) (fe' : Fun-Ext) where

 open import UF.H-Levels fe fe'

 module _ (te : H-level-truncations-exist) (𝓥 : Universe) where

\end{code}

We begin by giving some definitions that Dan uses in his paper. We will use
𝓥 as our point of reference for 'smallness'.

\begin{code}

  _is_locally-small : (X : 𝓤 ̇) → (n : ℕ) → 𝓤 ⊔ (𝓥 ⁺) ̇
  X is zero locally-small = X is 𝓥 small
  X is (succ n) locally-small = (x x' : X) → (x ＝ x') is n locally-small

\end{code}

We will now begin proving some of the results of the paper. We will attempt to
avoid any unnecesay use of propositional resizing. Theorem numbers will be
provided for easy reference.

WARNING: Be aware that our definitions are 'off by two' which results from our
choice of H-levels.

Proposition 2.2.

\begin{code}

  open H-level-truncations-exist te
  open k-connectedness te

  Join-Construction-Result : {𝓤 𝓦 : Universe} {A : 𝓤 ̇} {X : 𝓦 ̇}
                           → (𝓥 ⁺) ⊔ 𝓤 ⊔ 𝓦 ̇
  Join-Construction-Result {𝓤} {𝓦} {A} {X} = (f : A → X)
                                           → A is 𝓥 small
                                           → X is 1 locally-small
                                           → map f is 1 connected
                                           → X is 𝓥 small

  Prop-2-2 : {𝓤 𝓦 : Universe} {A : 𝓤 ̇} {X : 𝓦 ̇}
           → (f : A → X)
           → (n : ℕ)
           → map f is n connected
           → A is 𝓥 small
           → X is n locally-small
           → Join-Construction-Result {𝓤} {𝓦} {A} {X}
           → X is 𝓥 small
  Prop-2-2 f zero f-is-con A-small X-is-loc-small j = X-is-loc-small
  Prop-2-2 f (succ n) f-is-con A-small X-is-loc-small j =
    j f A-small {!!} {!!}

\end{code}

The inductive step follows from a result in Egbert's "The Join
Construction". Unfortunately, these results have yet to be implemented in the
TypeTopology library. For now we maintain that the above result follows from
Egbert's result.

TODO: Show connectedness is downward cummulative and that X is locally small.

Lemma 2.3.

\begin{code}

  Lemma-2-3 : {X : 𝓤 ̇} (n : ℕ)
            → X is-of-hlevel (succ n)
            → X is n locally-small
  Lemma-2-3 n X-hlevel = {!!}

\end{code}

Lemma 2.4.

\begin{code}

  Lemma-2-4 : {X : 𝓤 ̇} {Y : 𝓦 ̇}
            → (f : X → Y)
            → (n : ℕ)
            → map f is-of-hlevel (succ n)
            → Y is n locally-small
            → X is n locally-small
  Lemma-2-4 = {!!}

\end{code}

Lemma 2.5.

\begin{code}

  Lemma-2-5 : {X : 𝓤 ̇} {Y : 𝓦 ̇}
            → (f : X → Y)
            → (n : ℕ)
            → map f is-of-hlevel (succ n)
            → Y is n locally-small
            → X is n connected
            → X is 𝓥 small
  Lemma-2-5 = {!!}

\end{code}

Theorem 2.6.

\begin{code}

  Theorem-2-6 : {X : 𝓤 ̇} {Y : 𝓦 ̇}
              → (n : ℕ)
              → (X is 𝓥 small)
              ↔ (X is n locally-small) × ((∣∣ X ∣∣ (succ n)) is 𝓥 small) 
  Theorem-2-6 = {!!}

\end{code}

Corollary 2.7.

\begin{code}

  Corollary-2-7 : {X : 𝓤 ̇} {Y : 𝓦 ̇}
                → (f : X → Y)
                → (n : ℕ)
                → map f is-of-hlevel (succ n)
                → Y is n locally-small
                → (∣∣ X ∣∣ (succ n)) is 𝓥 small
                → X is 𝓥 small
  Corollary-2-7 = {!!}

\end{code}

TODO: Proposition 2.8. requires the concept of Homotopy Groups.


