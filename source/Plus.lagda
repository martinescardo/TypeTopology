The disjoint sum X + Y of two types X and Y.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Plus where

open import Universes

data _+_ {𝓤 𝓥} (X : 𝓤 ̇) (Y : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
  inl : X → X + Y
  inr : Y → X + Y

dep-cases : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : X + Y → 𝓦 ̇}
          → ((x : X) → A(inl x))
          → ((y : Y) → A(inr y))
          → ((z : X + Y) → A z)
dep-cases f g (inl x) = f x
dep-cases f g (inr y) = g y

cases : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇} → (X → A) → (Y → A) → X + Y → A
cases = dep-cases

Cases : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇} → X + Y → (X → A) → (Y → A) → A
Cases z f g = cases f g z

\end{code}

Fixities:

\begin{code}

infixr 1 _+_

\end{code}
