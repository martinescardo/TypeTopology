Empty type.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Empty where

open import Universes

data 𝟘 {𝓤} : 𝓤 ̇  where
unique-from-𝟘 : {A : 𝓤 ̇} → 𝟘 {𝓥} → A
unique-from-𝟘 = λ ()

𝟘-elim = unique-from-𝟘

\end{code}
