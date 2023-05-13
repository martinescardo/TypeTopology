Martin Escardo 2012

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module EffectfulForcing.Combinators where

open import MLTT.Spartan

Ķ : {X Y : 𝓤 ̇ } → X → Y → X
Ķ x y = x

Ş : {X Y Z : 𝓤 ̇ } → (X → Y → Z) → (X → Y) → X → Z
Ş f g x = f x (g x)

iter : {X : 𝓤 ̇ } → (X → X) → X → ℕ → X
iter f x  zero    = x
iter f x (succ n) = f (iter f x n)

\end{code}
