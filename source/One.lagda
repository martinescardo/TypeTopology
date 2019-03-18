One element type.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module One where

open import Universes

data 𝟙 {𝓤} : 𝓤 ̇  where
 * : 𝟙

unique-to-𝟙 : {A : 𝓤 ̇} → A → 𝟙 {𝓥}
unique-to-𝟙 {𝓤} {𝓥} a = * {𝓥}

\end{code}
