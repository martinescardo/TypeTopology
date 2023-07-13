```agda

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import Notation.Order
open import Naturals.Order
open import TypeTopology.DiscreteAndSeparated
open import UF.Subsingletons
open import UF.Miscelanea
open import UF.Equiv
open import Fin.Variation
open import Fin.Order

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

_::_ : {T : ℕ → 𝓤 ̇ } → T 0 → Π (T ∘ succ) → Π T
(h :: α) 0 = h
(h :: α) (succ n) = α n

_∼ⁿ_ : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X) → ℕ → 𝓤 ̇
(α ∼ⁿ β) n = (i : ℕ) → i < n → α i ＝ β i

_≈ⁿ_ : {X : ℕ → 𝓤 ̇ } → Π X → Π X → ℕ → 𝓤 ̇
(α ≈ⁿ β) n = (i : ℕ) → i < n → α i ＝ β i

{- _≈ⁿ_ : {d : ℕ} {Y : Fin' (succ d) → 𝓤 ̇ } → Π Y → Π Y → Fin' (succ d) → 𝓤  ̇
_≈ⁿ_ {𝓤} {d} α β n = (i : Fin' (succ d)) → pr₁ i < pr₁ n → α i ＝ β i
-}
```
