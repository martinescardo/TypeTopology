sMartin Escardo 2012

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.MFPSAndVariations.Combinators where

open import MLTT.Spartan hiding (rec)

Ķ : {X Y : 𝓤 ̇ } → X → Y → X
Ķ x y = x

Ş : {X Y Z : 𝓤 ̇ } → (X → Y → Z) → (X → Y) → X → Z
Ş f g x = f x (g x)

iter : {X : 𝓤 ̇ } → (X → X) → X → ℕ → X
iter f x  0       = x
iter f x (succ n) = f (iter f x n)

rec : {X : 𝓤 ̇ } → (ℕ → X → X) → X → ℕ → X
rec f x  0       = x
rec f x (succ n) = f n (rec f x n)

\end{code}
