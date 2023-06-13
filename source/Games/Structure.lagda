Martin Escardo, Paulo Oliva, 2023

Structures on dependent type trees.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan hiding (J)

module Games.Structure
        {𝓤 : Universe}
        (S : Type → 𝓤 ̇  )
       where

open import Games.TypeTrees

structure : 𝕋 → 𝓤 ̇
structure []       = 𝟙
structure (X ∷ Xf) = S X × ((x : X) → structure (Xf x))

\end{code}
