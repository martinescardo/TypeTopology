Martin Escardo 23 February 2022

The pre-univalence axiom, first suggested by Evan Cavallo in November
2017 (see link below) and then again by Peter Lumsdaine in August 2023
verbally to me.

https://groups.google.com/g/homotopytypetheory/c/bKti7krHM-c/m/vxRU3FwADQAJ

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module UF.PreUnivalence where

open import MLTT.Spartan
open import UF.Equiv
open import UF.Embeddings

is-preunivalent : ∀ 𝓤 → 𝓤 ⁺ ̇
is-preunivalent 𝓤 = (X Y : 𝓤 ̇ ) → is-embedding (idtoeq X Y)

\end{code}
