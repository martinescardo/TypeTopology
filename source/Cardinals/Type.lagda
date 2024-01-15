Jon Sterling, 25th March 2023.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.SetTrunc
open import UF.Subsingletons

module Cardinals.Type (st : set-truncations-exist) where

open import UF.Embeddings
open import UF.Subsingletons-FunExt

import UF.Logic

open set-truncations-exist st

Card : (𝓤 : Universe) → 𝓤 ⁺ ̇
Card 𝓤 = set-trunc (hSet 𝓤)

Card-is-set : is-set (Card 𝓤)
Card-is-set = set-trunc-is-set

\end{code}
