Martin Escardo & Tom de Jong, July 2023.

More about iterative ordinals and their relation to iterative (multi)sets.

 * Assuming propositional resizing, Ord is retract of 𝕄 and a also a
   retract of 𝕍.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.Univalence

module Iterative.Ordinals-Addendum
        (ua : Univalence)
        {𝓤 : Universe}
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

open import InjectiveTypes.Blackboard fe'
open import Iterative.Multisets 𝓤
open import Iterative.Ordinals ua 𝓤
open import Iterative.Sets ua 𝓤
open import Ordinals.Injectivity
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type hiding (Ord)
open import UF.Embeddings
open import UF.Retracts
open import UF.Size

open ordinals-injectivity fe'

private
 e : Ordinal 𝓤 ↪ Ordinal 𝓤⁺
 e = Ordinal-embedded-in-next-Ordinal

 almost-a-retraction-𝕄 : Σ f ꞉ (𝕄 → Ordinal 𝓤⁺) , f ∘ Ord-to-𝕄 ∼ ⌊ e ⌋
 almost-a-retraction-𝕄 = Ordinal-is-ainjective (ua 𝓤⁺)
                          Ord-to-𝕄
                          Ord-to-𝕄-is-embedding
                          ⌊ e ⌋

 almost-a-retraction-𝕍 : Σ f ꞉ (𝕍 → Ordinal 𝓤⁺) , f ∘ Ord-to-𝕍 ∼ ⌊ e ⌋
 almost-a-retraction-𝕍 = Ordinal-is-ainjective (ua 𝓤⁺)
                          Ord-to-𝕍
                          Ord-to-𝕍-is-embedding
                          ⌊ e ⌋
\end{code}

To get retractions we would like to extend the identity functions,
rather than ⌊ e ⌋, but the universe levels get on the way. Unless we
assume propositional resizing.

\begin{code}

Ord-is-retract-of-𝕄 : propositional-resizing 𝓤⁺ 𝓤
                    → retract Ord of 𝕄
Ord-is-retract-of-𝕄 pe = embedding-retract Ord 𝕄 Ord-to-𝕄
                           Ord-to-𝕄-is-embedding
                           (ainjective-resizing {𝓤} {𝓤} pe (Ordinal 𝓤)
                             (Ordinal-is-ainjective (ua 𝓤)))

\end{code}

TODO. Can we get the same conclusion without propositional resizing?

\begin{code}

Ord-is-retract-of-𝕍 : propositional-resizing 𝓤⁺ 𝓤
                    → retract Ord of 𝕍
Ord-is-retract-of-𝕍 pe = embedding-retract Ord 𝕍 Ord-to-𝕍
                          Ord-to-𝕍-is-embedding
                          (ainjective-resizing {𝓤} {𝓤} pe (Ordinal 𝓤)
                            (Ordinal-is-ainjective (ua 𝓤)))
\end{code}

It is actually possible to prove this without propositional
resizing. For the retraction, we map an iterative set to its rank. For
this we need set quotients or, equivalently, set replacement. This is
done in [5] (see the list of references in the index file) for the
higher-inductive definition of 𝕍.
