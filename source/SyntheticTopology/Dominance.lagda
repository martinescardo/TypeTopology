\begin{code}

{-# OPTIONS --safe --without-K --exact-split --auto-inline #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.SubtypeClassifier

module SyntheticTopology.Dominance
        (𝓤  : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist) where

open import Dominance.Definition
open import SyntheticTopology.SierpinskiObject (𝓤 ⁺) fe pe pt
open import UF.Classifiers
open import UF.Embeddings
open import UF.Equiv
open import UF.ImageAndSurjection pt
open import UF.Logic
open import UF.Subsingletons-FunExt
open import UF.Univalence
open import UF.UniverseEmbedding

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)


\end{code}

We define several Sierpinski objects and prove that they are dominances.

1 : Ω 𝓤

\begin{code}

Ω-Sierpinski : Sierpinski-Object
Ω-Sierpinski = Ω 𝓤 , (λ P → (Lift (𝓤 ⁺) (P holds) , {!!} ) ), {!!}

\end{code}
