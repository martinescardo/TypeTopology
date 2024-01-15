Martin Escardo 23 February 2023

The pre-univalence axiom, first suggested by Evan Cavallo in November
2017 [1] and then again by Peter Lumsdaine in August 2022
verbally to me.

[1] https://groups.google.com/g/homotopytypetheory/c/bKti7krHM-c/m/vxRU3FwADQAJ

The preunivalence axiom is a common generalization of the univalence
axiom and the K axiom.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.PreUnivalence where

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.Sets
open import UF.Subsingletons
open import UF.Univalence

is-preunivalent : ∀ 𝓤 → 𝓤 ⁺ ̇
is-preunivalent 𝓤 = (X Y : 𝓤 ̇ ) → is-embedding (idtoeq X Y)

Preunivalence : 𝓤ω
Preunivalence = (𝓤 : Universe) → is-preunivalent 𝓤

univalence-gives-preunivalence : is-univalent 𝓤
                               → is-preunivalent 𝓤
univalence-gives-preunivalence ua X Y = equivs-are-embeddings
                                         (idtoeq X Y)
                                         (ua X Y)

Univalence-gives-Preunivalence : Univalence → Preunivalence
Univalence-gives-Preunivalence ua 𝓤 = univalence-gives-preunivalence (ua 𝓤)

K-gives-preunivalence : K-axiom 𝓤
                      → K-axiom (𝓤 ⁺)
                      → is-preunivalent 𝓤
K-gives-preunivalence {𝓤} k k' X Y e (p , _) (p' , _) =
 to-subtype-＝ (λ _ → k (X ≃ Y)) (k' (𝓤  ̇ )p p')

K-gives-Preunivalence : K-Axiom → Preunivalence
K-gives-Preunivalence k 𝓤 = K-gives-preunivalence (k 𝓤) (k (𝓤 ⁺))

\end{code}
