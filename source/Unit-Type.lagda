\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Unit-Type where

open import Universes public

data 𝟙 {𝓤} : 𝓤 ̇ where
 ⋆ : 𝟙

\end{code}
