Martin Escardo, 19th Feb 2019.

This is an article-style version of the blackboard-style version.

This is based on the "blackboard" Agda file InjectiveTypes, which
presents the ideas as they have been developed, rather than the way
they should be presented for a mathematical audience, but still in a
fully verified way with the computer as the referee.

Here we tell the story, referring to the blackboard file for the
proofs (which can be followed as links in the html version of this
file).

The blackboard file likely has more information than that reported
here.

Here we repeat the main definitions (in a definitionally equal way,
even with the same names) and state the main theorems with links to
their blackboard (verified) proofs.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Univalence
open import UF-PropTrunc

module InjectiveTypes-article
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import SpartanMLTT
open import Plus-Properties
open import UF-FunExt
open import UF-UA-FunExt
open import UF-Base
open import UF-Equiv
open import UF-Embeddings
open import UF-Retracts
open import UF-EquivalenceExamples
open import UF-Univalence
open import UF-IdEmbedding
open import UF-PropIndexedPiSigma
open import UF-Subsingletons
open import UF-Resizing
open import UF-UniverseEmbedding
open import UF-ExcludedMiddle


import InjectiveTypes

fe : FunExt
fe = FunExt-from-Univalence ua

pe : PropExt
pe 𝓤 = propext-from-univalence (ua 𝓤)

\end{code}

We first define injective types, moderately injective types, and
weakly injective types.

\begin{code}

injective-type : 𝓦 ̇ → (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥  ⁺ ⊔ 𝓦 ̇
injective-type D 𝓤 𝓥 = {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y) → is-embedding j
                     → (f : domain j → D) → Σ \(f' : codomain j → D) → f' ∘ j ∼ f

minjective-type : 𝓦 ̇ → (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥  ⁺ ⊔ 𝓦 ̇
minjective-type D 𝓤 𝓥 = ∥ injective-type D 𝓤 𝓥 ∥

winjective-type : 𝓦 ̇ → (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥  ⁺ ⊔ 𝓦 ̇
winjective-type D 𝓤 𝓥 = {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y) → is-embedding j
                      → (f : X → D) → ∃ \(f' : Y → D) → f' ∘ j ∼ f

\end{code}

Universes are injective:

\begin{code}

universes-are-injective : injective-type (𝓤 ⊔ 𝓥 ̇) 𝓤 𝓥
universes-are-injective {𝓤} {𝓥} = InjectiveTypes.universes-are-injective-Π fe (ua (𝓤 ⊔ 𝓥))

universes-are-injective-particular : injective-type (𝓤 ̇) 𝓤 𝓤
universes-are-injective-particular = universes-are-injective

\end{code}

Retracts of injective are injective:

\begin{code}

retract-of-injective : (D' : 𝓦' ̇) (D : 𝓦 ̇)
                     → injective-type D 𝓤 𝓥
                     → retract D' of D
                     → injective-type D' 𝓤 𝓥
retract-of-injective = InjectiveTypes.retract-of-injective fe

\end{code}

Products of injectives are injectives:

\begin{code}

product-of-injective : {A : 𝓣 ̇} {D : A → 𝓦 ̇}
                     → ((a : A) → injective-type (D a) 𝓤 𝓥)
                     → injective-type (Π D) 𝓤 𝓥
product-of-injective = InjectiveTypes.product-of-injective fe

\end{code}

Hence exponential powers of injectives are injective.

\begin{code}

power-of-injective : {A : 𝓣 ̇} {D : 𝓦 ̇}
                   → injective-type D 𝓤 𝓥
                   → injective-type (A → D) 𝓤 𝓥
power-of-injective i = product-of-injective (λ a → i)

\end{code}

An injective type is a retract of every type it is embedded into:

\begin{code}

injective-retract-of-subtype : (D : 𝓦 ̇) → injective-type D 𝓦 𝓥
                             → (Y : 𝓥 ̇) → D ↪ Y → retract D of Y
injective-retract-of-subtype D i Y (j , e) = InjectiveTypes.embedding-retract fe D Y j e i

\end{code}

The identity-type former is an embedding X → (X → 𝓤):

\begin{code}

Id-is-embedding : {X : 𝓤 ̇} → is-embedding(Id {𝓤} {X})
Id-is-embedding {𝓤} = UA-Id-embedding (ua 𝓤) fe

\end{code}

From this we conclude that

\begin{code}

injective-is-retract-of-power-of-universe : (D : 𝓤 ̇)
                                          → injective-type D 𝓤  (𝓤 ⁺)
                                          → retract D of (D → 𝓤 ̇)
injective-is-retract-of-power-of-universe {𝓤} D i = injective-retract-of-subtype D i (D → 𝓤 ̇)
                                                      (Id , Id-is-embedding)

\end{code}

From this we further conclude that we can reduce a universe level and
still have injectivity:

\begin{code}

injective-resizing₀ : (D : 𝓤 ̇) → injective-type D 𝓤 (𝓤 ⁺) → injective-type D 𝓤 𝓤
injective-resizing₀ {𝓤} D i = φ (injective-is-retract-of-power-of-universe D i)
 where
  φ : retract D of (D → 𝓤 ̇) → injective-type D 𝓤 𝓤
  φ = retract-of-injective D (D → 𝓤 ̇) (power-of-injective (universes-are-injective))

\end{code}

Much more to follow, taking from the blackboard... under construction.
