\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module MLTT.Unit-Type where

open import MLTT.Universes public

data 𝟙 {𝓤} : 𝓤 ̇ where
 ⋆ : 𝟙

\end{code}
