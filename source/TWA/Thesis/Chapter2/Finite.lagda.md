# Finite types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import TypeTopology.DiscreteAndSeparated
open import UF.Subsingletons
open import UF.Miscelanea
open import UF.Equiv
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Fin.Type
open import Fin.Bishop

module TWA.Thesis.Chapter2.Finite where

Fin-is-discrete : (n : ℕ) → is-discrete (Fin n)
Fin-is-discrete 0 = 𝟘-is-discrete
Fin-is-discrete (succ n)
 = +-is-discrete (Fin-is-discrete n) 𝟙-is-discrete

Fin-is-set : (n : ℕ) → is-set (Fin n)
Fin-is-set (succ n) = +-is-set (Fin n) 𝟙 (Fin-is-set n) 𝟙-is-set

finite-is-discrete
 : {F : 𝓤 ̇ } → (f : finite-linear-order F) → is-discrete F
finite-is-discrete (n , f)
 = equiv-to-discrete (≃-sym f) (Fin-is-discrete n)

finite-is-set : {F : 𝓤 ̇ } → (f : finite-linear-order F) → is-set F
finite-is-set (n , f) = equiv-to-set f (Fin-is-set n)

𝟚-is-finite : finite-linear-order 𝟚
𝟚-is-finite = 2 , qinveq g (h , η , μ)
 where
  g : 𝟚 → Fin 2
  g ₀ = 𝟎
  g ₁ = 𝟏
  h : Fin 2 → 𝟚
  h 𝟎 = ₀
  h 𝟏 = ₁
  η : h ∘ g ∼ id
  η ₀ = refl
  η ₁ = refl
  μ : g ∘ h ∼ id
  μ 𝟎 = refl
  μ 𝟏 = refl
```
