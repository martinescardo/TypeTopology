[⇐ Index](../html/TWA.Thesis.index.html)

# Finite types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.DiscreteAndSeparated
open import UF.Subsingletons
open import UF.Sets
open import UF.Sets-Properties
open import UF.Equiv
open import UF.EquivalenceExamples
open import Fin.Type
open import Fin.Bishop
open import Fin.ArithmeticViaEquivalence
open import MLTT.SpartanList

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

𝟙-is-finite : finite-linear-order (𝟙 {𝓦})
𝟙-is-finite = 1 , qinveq g (h , η , μ)
 where
  g : 𝟙 → Fin 1
  g ⋆ = 𝟎
  h : Fin 1 → 𝟙
  h 𝟎 = ⋆
  η : h ∘ g ∼ id
  η ⋆ = refl 
  μ : g ∘ h ∼ id
  μ 𝟎 = refl
  μ (suc ())

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

+-is-finite : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            → finite-linear-order X
            → finite-linear-order Y
            → finite-linear-order (X + Y)
+-is-finite (n , e) (m , f)
 = n +' m , (+-cong e f ● ≃-sym (Fin+homo n m))

×-is-finite : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            → finite-linear-order X
            → finite-linear-order Y
            → finite-linear-order (X × Y)
×-is-finite (n , e) (m , f)
 = n ×' m , (×-cong e f ● ≃-sym (Fin×homo n m))

vec-is-finite : (ϵ : ℕ) {F : Fin ϵ → 𝓤 ̇ }
              → (f : (n : Fin ϵ) → finite-linear-order (F n))
              → finite-linear-order (vec ϵ F)
vec-is-finite 0 f = 𝟙-is-finite
vec-is-finite (succ ϵ) f
 = ×-is-finite (f 𝟎) (vec-is-finite ϵ (f ∘ suc))

pointed : 𝓤 ̇ → 𝓤 ̇
pointed X = X
```

[⇐ Index](../html/TWA.Thesis.index.html)
