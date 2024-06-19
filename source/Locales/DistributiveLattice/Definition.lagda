---
title:         Distributive lattices
author:        Ayberk Tosun
date-started:  2024-02-14
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets

module Locales.DistributiveLattice.Definition
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open import Locales.Frame pt fe
open import MLTT.Spartan
open import UF.Base
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.SubtypeClassifier

open Implication fe

\end{code}

We give the equational definition from Stone Spaces.

\begin{code}

record DistributiveLattice (𝓤 : Universe) : 𝓤 ⁺  ̇ where
 field
  X   : 𝓤  ̇
  𝟏   : X
  𝟎   : X
  _∧_ : X → X → X
  _∨_ : X → X → X

 field
  X-is-set      : is-set X

  ∧-associative : (x y z : X) → x ∧ (y ∧ z) ＝ (x ∧ y) ∧ z
  ∧-commutative : (x y   : X) → x ∧ y ＝ y ∧ x
  ∧-unit        : (x     : X) → x ∧ 𝟏 ＝ x
  ∧-idempotent  : (x     : X) → x ∧ x ＝ x
  ∧-absorptive  : (x y   : X) → x ∧ (x ∨ y) ＝ x

  ∨-associative : (x y z : X) → x ∨ (y ∨ z) ＝ (x ∨ y) ∨ z
  ∨-commutative : (x y   : X) → x ∨ y ＝ y ∨ x
  ∨-unit        : (x     : X) → x ∨ 𝟎 ＝ x
  ∨-idempotent  : (x     : X) → x ∨ x ＝ x
  ∨-absorptive  : (x y   : X) → x ∨ (x ∧ y) ＝ x

  distributivityᵈ : (x y z : X) → x ∧ (y ∨ z) ＝ (x ∧ y) ∨ (x ∧ z)

\end{code}

Some easy lemmas that we prove directly inside the record definition.

\begin{code}

 distributivityᵈ₁ : (x y z : X) → (y ∨ z) ∧ x ＝ (y ∧ x) ∨ (z ∧ x)
 distributivityᵈ₁ x y z = (y ∨ z) ∧ x         ＝⟨ Ⅰ ⟩
                          x ∧ (y ∨ z)         ＝⟨ Ⅱ ⟩
                          (x ∧ y) ∨ (x ∧ z)   ＝⟨ Ⅲ ⟩
                          (y ∧ x) ∨ (x ∧ z)   ＝⟨ Ⅳ ⟩
                          (y ∧ x) ∨ (z ∧ x)   ∎
                           where
                            Ⅰ = ∧-commutative (y ∨ z) x
                            Ⅱ = distributivityᵈ x y z
                            Ⅲ = ap (_∨ (x ∧ z)) (∧-commutative x y)
                            Ⅳ = ap ((y ∧ x) ∨_) (∧-commutative x z)

 ∨-unit₁ : (x : X) → 𝟎 ∨ x ＝ x
 ∨-unit₁ x = 𝟎 ∨ x   ＝⟨ ∨-commutative 𝟎 x ⟩
             x ∨ 𝟎   ＝⟨ ∨-unit x          ⟩
             x       ∎

 ∧-absorptive₁ : (x y : X) → x ∧ (y ∨ x) ＝ x
 ∧-absorptive₁ x y = x ∧ (y ∨ x) ＝⟨ ap (x ∧_) (∨-commutative y x) ⟩
                     x ∧ (x ∨ y) ＝⟨ ∧-absorptive x y              ⟩
                     x           ∎

 ∨-absorptive₁ : (x y : X) → x ∨ (y ∧ x) ＝ x
 ∨-absorptive₁ x y = x ∨ (y ∧ x) ＝⟨ ap (x ∨_) (∧-commutative y x) ⟩
                     x ∨ (x ∧ y) ＝⟨ ∨-absorptive x y              ⟩
                     x ∎

 ∨-absorptive₂ : (x y : X) → (x ∧ y) ∨ x ＝ x
 ∨-absorptive₂ x y = (x ∧ y) ∨ x ＝⟨ ∨-commutative (x ∧ y) x ⟩
                     x ∨ (x ∧ y) ＝⟨ ∨-absorptive x y        ⟩
                     x           ∎

 ∧-absorptive₃ : (x y : X) → (y ∨ x) ∧ x ＝ x
 ∧-absorptive₃ x y = (y ∨ x) ∧ x ＝⟨ ∧-commutative (y ∨ x) x ⟩
                     x ∧ (y ∨ x) ＝⟨ ∧-absorptive₁ x y       ⟩
                     x           ∎

 ∨-absorptive₃ : (x y : X) → (y ∧ x) ∨ x ＝ x
 ∨-absorptive₃ x y = (y ∧ x) ∨ x ＝⟨ Ⅰ ⟩
                     (x ∧ y) ∨ x ＝⟨ Ⅱ ⟩
                     x           ∎
                      where
                       Ⅰ = ap (_∨ x) (∧-commutative y x)
                       Ⅱ = ∨-absorptive₂ x y

\end{code}

Notation for the carrier set.

\begin{code}

∣_∣ᵈ : DistributiveLattice 𝓤 → 𝓤  ̇
∣_∣ᵈ L = let open DistributiveLattice L in X

\end{code}

The dual of the distributivity law.

\begin{code}

module _ (L : DistributiveLattice 𝓤) where

 open DistributiveLattice L

 distributivity-op : (x y z : ∣ L ∣ᵈ) → x ∨ (y ∧ z) ＝ (x ∨ y) ∧ (x ∨ z)
 distributivity-op x y z =
  x ∨ (y ∧ z)              ＝⟨ Ⅰ ⟩
  x ∨ ((z ∧ y) ∨ (z ∧ x))  ＝⟨ Ⅱ ⟩
  (x ∨ z) ∧ (y ∨ x)        ＝⟨ Ⅲ ⟩
  (y ∨ x) ∧ (x ∨ z)        ＝⟨ Ⅳ ⟩
  (x ∨ y) ∧ (x ∨ z)        ∎
   where
    𝒶 = ap (_∨ (y ∧ z)) (∨-absorptive₁ x z ⁻¹)
    𝒷 = ap ((x ∨ (z ∧ x)) ∨_) (∧-commutative y z)
    𝒸 = ∨-associative x (z ∧ x) (z ∧ y) ⁻¹
    𝒹 = ap (x ∨_) (∨-commutative (z ∧ x) (z ∧ y))
    ℯ = ap (x ∨_) (distributivityᵈ z y x ⁻¹)
    𝒻 = ap (_∨ (z ∧ (y ∨ x))) (∧-absorptive₁ x y ⁻¹)
    ℊ = distributivityᵈ₁ (y ∨ x) x z ⁻¹

    Ⅰ = x ∨ (y ∧ z)                   ＝⟨ 𝒶 ⟩
        (x ∨ (z ∧ x)) ∨ (y ∧ z)       ＝⟨ 𝒷 ⟩
        (x ∨ (z ∧ x)) ∨ (z ∧ y)       ＝⟨ 𝒸 ⟩
        x ∨ ((z ∧ x) ∨ (z ∧ y))       ＝⟨ 𝒹 ⟩
        x ∨ ((z ∧ y) ∨ (z ∧ x))       ∎
    Ⅱ = x ∨ ((z ∧ y) ∨ (z ∧ x))       ＝⟨ ℯ ⟩
        x ∨ (z ∧ (y ∨ x))             ＝⟨ 𝒻 ⟩
        (x ∧ (y ∨ x)) ∨ (z ∧ (y ∨ x)) ＝⟨ ℊ ⟩
        (x ∨ z) ∧ (y ∨ x)             ∎
    Ⅲ = ∧-commutative (x ∨ z) (y ∨ x)
    Ⅳ = ap (_∧ (x ∨ z)) (∨-commutative y x)

\end{code}

Definition of the order as `x ≤ y := x ∧ y = x`.

\begin{code}

orderᵈ-∧ : (L : DistributiveLattice 𝓤) → ∣ L ∣ᵈ → ∣ L ∣ᵈ → Ω 𝓤
orderᵈ-∧ L x y = (x ∧ y ＝ x) , X-is-set
 where
  open DistributiveLattice L

\end{code}

We take this as our primary order.

\begin{code}

syntax orderᵈ-∧ L x y = x ≤ᵈ[ L ] y

≤ᵈ-is-reflexive : (L : DistributiveLattice 𝓤) → is-reflexive (orderᵈ-∧ L) holds
≤ᵈ-is-reflexive L = ∧-idempotent
 where
  open DistributiveLattice L

≤ᵈ-is-transitive : (L : DistributiveLattice 𝓤) → is-transitive (orderᵈ-∧ L) holds
≤ᵈ-is-transitive L x y z p q =
 x ∧ z         ＝⟨ Ⅰ ⟩
 (x ∧ y) ∧ z   ＝⟨ Ⅱ ⟩
 x ∧ (y ∧ z)   ＝⟨ Ⅲ ⟩
 x ∧ y         ＝⟨ Ⅳ ⟩
 x             ∎
  where
   open DistributiveLattice L

   Ⅰ = ap (_∧ z) (p ⁻¹)
   Ⅱ = ∧-associative x y z ⁻¹
   Ⅲ = ap (x ∧_) q
   Ⅳ = p

≤ᵈ-is-antisymmetric : (L : DistributiveLattice 𝓤) → is-antisymmetric (orderᵈ-∧ L)
≤ᵈ-is-antisymmetric L {x} {y} p q =
 x      ＝⟨ Ⅰ ⟩
 x ∧ y  ＝⟨ Ⅱ ⟩
 y ∧ x  ＝⟨ Ⅲ ⟩
 y      ∎
  where
   open DistributiveLattice L

   Ⅰ = p ⁻¹
   Ⅱ = ∧-commutative x y
   Ⅲ = q

\end{code}

It is also useful to have the alternative definition `x ≤ y := x ∨ y ＝ y`.

\begin{code}

orderᵈ-∨ : (L : DistributiveLattice 𝓤) → ∣ L ∣ᵈ → ∣ L ∣ᵈ → Ω 𝓤
orderᵈ-∨ L x y = (x ∨ y ＝ y) , X-is-set
 where
  open DistributiveLattice L

syntax orderᵈ-∨ L x y = x ≤ᵈ[ L ]₀ y

orderᵈ-∨-implies-orderᵈ : (L : DistributiveLattice 𝓤) {x y : ∣ L ∣ᵈ}
                        → (x ≤ᵈ[ L ]₀ y ⇒ x ≤ᵈ[ L ] y) holds
orderᵈ-∨-implies-orderᵈ L {x} {y} p =
 x ∧ y ＝⟨ Ⅰ ⟩ x ∧ (x ∨ y) ＝⟨ Ⅱ ⟩ x ∎
  where
   open DistributiveLattice L

   Ⅰ = ap (x ∧_) p ⁻¹
   Ⅱ = ∧-absorptive x y

orderᵈ-implies-orderᵈ-∨ : (L : DistributiveLattice 𝓤) {x y : ∣ L ∣ᵈ}
                        → (x ≤ᵈ[ L ] y ⇒ x ≤ᵈ[ L ]₀ y) holds
orderᵈ-implies-orderᵈ-∨ L {x} {y} p =
 x ∨ y       ＝⟨ Ⅰ                ⟩
 y ∨ x       ＝⟨ Ⅱ                ⟩
 y ∨ (x ∧ y) ＝⟨ Ⅲ                ⟩
 y ∨ (y ∧ x) ＝⟨ ∨-absorptive y x ⟩
 y           ∎
  where
   open DistributiveLattice L

   Ⅰ = ∨-commutative x y
   Ⅱ = ap (y ∨_) (p ⁻¹)
   Ⅲ = ap (y ∨_) (∧-commutative x y)

\end{code}

We package everything up into a poset.

\begin{code}

poset-ofᵈ : DistributiveLattice 𝓤 → Poset 𝓤 𝓤
poset-ofᵈ L = ∣ L ∣ᵈ
            , orderᵈ-∧ L
            , (≤ᵈ-is-reflexive L , ≤ᵈ-is-transitive L)
            , ≤ᵈ-is-antisymmetric L
 where
  open DistributiveLattice L

\end{code}

Finally, we show that the operations `_∧_` and `_∨_` are indeed meets and
join operations.

\begin{code}

module _ (L : DistributiveLattice 𝓤) where

 open DistributiveLattice L
 open Meets (orderᵈ-∧ L)
 open Joins (orderᵈ-∧ L)

 𝟏ᵈ-is-top : (x : X) → (x ≤ᵈ[ L ] 𝟏) holds
 𝟏ᵈ-is-top = ∧-unit

 𝟎ᵈ-is-bottom : (x : X) → (𝟎 ≤ᵈ[ L ] x) holds
 𝟎ᵈ-is-bottom x = orderᵈ-∨-implies-orderᵈ L (∨-unit₁ x)

 only-𝟎-is-below-𝟎ᵈ : (x : X) → (x ≤ᵈ[ L ] 𝟎) holds → x ＝ 𝟎
 only-𝟎-is-below-𝟎ᵈ x p =
  ≤-is-antisymmetric (poset-ofᵈ L) p (𝟎ᵈ-is-bottom x)

 ∧-is-a-lower-bound₂ : (x y : X) → ((x ∧ y) ≤ᵈ[ L ] y) holds
 ∧-is-a-lower-bound₂ x y = (x ∧ y) ∧ y ＝⟨ Ⅰ ⟩
                           x ∧ (y ∧ y) ＝⟨ Ⅱ ⟩
                           x ∧ y ∎
                            where
                             Ⅰ = ∧-associative x y y ⁻¹
                             Ⅱ = ap (x ∧_) (∧-idempotent y)


 ∧-is-a-lower-bound₁ : (x y : X) → ((x ∧ y) ≤ᵈ[ L ] x) holds
 ∧-is-a-lower-bound₁ x y = (x ∧ y) ∧ x   ＝⟨ Ⅰ ⟩
                           (y ∧ x) ∧ x   ＝⟨ Ⅱ ⟩
                           y ∧ (x ∧ x)   ＝⟨ Ⅲ ⟩
                           y ∧ x         ＝⟨ Ⅳ ⟩
                           x ∧ y          ∎
                            where
                             Ⅰ = ap (_∧ x) (∧-commutative x y)
                             Ⅱ = ∧-associative y x x ⁻¹
                             Ⅲ = ap (y ∧_) (∧-idempotent x)
                             Ⅳ = ∧-commutative y x


 ∧-is-greatest : (x y z : ∣ L ∣ᵈ)
               → (z is-a-lower-bound-of (x , y) ⇒ z ≤ᵈ[ L ] (x ∧ y)) holds
 ∧-is-greatest x y z (p₁ , p₂) = z ∧ (x ∧ y)    ＝⟨ Ⅰ ⟩
                                 (z ∧ x) ∧ y    ＝⟨ Ⅱ ⟩
                                 z ∧ y          ＝⟨ Ⅲ ⟩
                                 z              ∎
                                  where
                                   Ⅰ = ∧-associative z x y
                                   Ⅱ = ap (_∧ y) p₁
                                   Ⅲ = p₂

 ∧-is-glb : (x y : ∣ L ∣ᵈ) → ((x ∧ y) is-glb-of (x , y)) holds
 ∧-is-glb x y = (∧-is-a-lower-bound₁ x y , ∧-is-a-lower-bound₂ x y)
              , λ (z , p) → ∧-is-greatest x y z p

\end{code}

\begin{code}

 ∨-is-an-upper-bound₁ : (x y : ∣ L ∣ᵈ) → (x ≤ᵈ[ L ] (x ∨ y)) holds
 ∨-is-an-upper-bound₁ = ∧-absorptive

 ∨-is-an-upper-bound₂ : (x y : ∣ L ∣ᵈ) → (y ≤ᵈ[ L ] (x ∨ y)) holds
 ∨-is-an-upper-bound₂ x y = ∧-absorptive₁ y x

 ∨-is-least : (x y z : ∣ L ∣ᵈ) → (z is-an-upper-bound-of₂ (x , y) ⇒ (x ∨ y) ≤ᵈ[ L ] z) holds
 ∨-is-least x y z (p₁ , p₂) = orderᵈ-∨-implies-orderᵈ L †
  where
   q₂ : y ∨ z ＝ z
   q₂ = orderᵈ-implies-orderᵈ-∨ L p₂

   q₁ : x ∨ z ＝ z
   q₁ = orderᵈ-implies-orderᵈ-∨ L p₁

   Ⅰ = ∨-associative x y z ⁻¹
   Ⅱ = ap (x ∨_) q₂
   Ⅲ = q₁

   † : (x ∨ y) ∨ z ＝ z
   † = (x ∨ y) ∨ z   ＝⟨ Ⅰ ⟩
       x ∨ (y ∨ z)   ＝⟨ Ⅱ ⟩
       x ∨ z         ＝⟨ Ⅲ ⟩
       z ∎

 ∨-is-lub : (x y : ∣ L ∣ᵈ) → ((x ∨ y) is-lub-of₂ (x , y)) holds
 ∨-is-lub x y = (∨-is-an-upper-bound₁ x y , ∨-is-an-upper-bound₂ x y)
              , λ (z , p) → ∨-is-least x y z p

\end{code}
