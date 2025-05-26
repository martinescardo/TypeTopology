Martin Escardo, 22nd October 2024 - 22 May 2025

This file is work in progress and aims to eventually subsume the file
gist.InjectivesVersusAlgebras (at which point that file will be deleted).

We give conditions on algebraic injective structure on a type so that
it coincides with the algebraic structure for the partial-map
classifier (aka lifting) monad 𝓛 on types.

We call these conditions "stability under composition" and "pullback
naturality".

Stability under composition says that an extension (f|j)|k of an
extension f|j is the extension f|(k∘j) along the composition of the
embeddings j and k, as in the following commutative diagram.


                   j         k
              X ──────→ Y ──────→ Z
               ╲        │        ╱
                ╲       │       ╱
             f   ╲      │ f|j  ╱ (f|j)|k = f(k∘j
                  ╲     │     ╱
                   ╲    │    ╱
                    ╲   │   ╱
                     ➘  ↓  ↙
                        D

Pullback naturality is expressed by the following diagram, where the
square is a pullback and j (and hence k) is an embedding.

                   k
              A ──────→ B
              │ ⌟       │
           g  │         │ h
              │         │
              ↓    j    ↓
              X ──────→ Y
               ╲        │
                ╲       │
             f   ╲      │ f|j ∘ h = (f ∘ g) | k
                  ╲     │
                   ╲    │
                    ╲   │
                     ➘  ↓
                        D

It actually suffices to consider pullbacks of the form


        fiber j y ────→ 𝟙
              │ ⌟       │
              │         │ y
              │         │
              ↓    j    ↓
              X ──────→ Y

One may wonder whether it is reasonable to consider naturality with
respect to all commutative squares

                   k
              A ──────→ B
              │         │
           g  │         │ h
              │         │
              ↓    j    ↓
              X ──────→ Y

where j and k are embeddings, but which are not necessarily
pullbacks. However, a counter-example is the commutative square


              𝟘 ──────→ 𝟙
              │         │
              │         │
              │         │
              ↓         ↓
              𝟙 ──────→ 𝟙

Finally, notice that 𝓛-algebraic structure is, by definition,
flabbiness structure plus an associativity law on this structure.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt

module InjectiveTypes.Algebra
        (fe : FunExt)
       where

fe' : Fun-Ext
fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Univalence
open import InjectiveTypes.Blackboard fe hiding (ηΠ ; ηΣ)

module _ {𝓤 𝓦 : Universe}
         (D : 𝓦 ̇ )
         (D-ainj : ainjective-type D 𝓤 𝓤)
       where

 _∣_ : {X Y : 𝓤 ̇ } → (X → D) → (X ↪ Y) → (Y → D)
 f ∣ 𝕛 = extension' D-ainj 𝕛 f

 stability-under-composition : 𝓦 ⊔ 𝓤 ⁺ ̇
 stability-under-composition =
    {X Y Z : 𝓤 ̇ } (f : X → D) (𝕛 : X ↪ Y) (𝕜 : Y ↪ Z)
  → f ∣ (𝕜 ∘↪ 𝕛) ∼ (f ∣ 𝕛) ∣ 𝕜

\end{code}

To be continued, following gist.InjectivesVersusAlgebras.
