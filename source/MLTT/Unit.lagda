Martin Escardo, original date unknown.

One element type.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Unit where

open import MLTT.Universes

record 𝟙 {𝓤} : 𝓤 ̇ where
 constructor
  ⋆

open 𝟙 public

unique-to-𝟙 : {A : 𝓤 ̇ } → A → 𝟙 {𝓥}
unique-to-𝟙 {𝓤} {𝓥} a = ⋆ {𝓥}

\end{code}
