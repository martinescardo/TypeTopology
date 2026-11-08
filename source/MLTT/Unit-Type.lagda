Martin Escardo, original date unknown.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Unit-Type where

open import MLTT.Universes public

data 𝟙 {𝓤} : 𝓤 ̇ where
 ⋆ : 𝟙

\end{code}
