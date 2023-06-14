\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import Notation.Order
open import Naturals.Order
open import TypeTopology.DiscreteAndSeparated
open import UF.Subsingletons
open import UF.Miscelanea
open import UF.Equiv

module TWA.Thesis.Chapter2.Sequences where

map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
    → (X → Y) → (ℕ → X) → (ℕ → Y)
map f α n = f (α n)

zipWith : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
        → (X → Y → Z) → (ℕ → X) → (ℕ → Y) → (ℕ → Z)
zipWith f α β n = f (α n) (β n)

head : {X : 𝓤 ̇ } → (ℕ → X) → X
head α = α 0

tail : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X)
tail α = α ∘ succ

_∶∶_ : {X : 𝓤 ̇ } → X → (ℕ → X) → (ℕ → X)
(h ∶∶ α) 0 = h
(h ∶∶ α) (succ n) = α n

\end{code}
