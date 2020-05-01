\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Identity-Type where

open import Universes

data _≡_ {𝓤} {X : 𝓤 ̇ } : X → X → 𝓤 ̇ where
  refl : {x : X} → x ≡ x

\end{code}
