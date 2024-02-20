---
title:       Distributive lattices
author:      Ayberk Tosun
start-date:  2024-02-14
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

In the future, equivalent definitions of the notion of distributive lattice
will be added to this module.

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

 _≤_ : X → X → Ω 𝓤
 x ≤ y = (x ∧ y ＝ x) , X-is-set

 ∧-is-a-lower-bound₁ : (x y : X) → ((x ∧ y) ≤ x) holds
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

 ∧-is-a-lower-bound₂ : (x y : X) → ((x ∧ y) ≤ y) holds
 ∧-is-a-lower-bound₂ x y = (x ∧ y) ∧ y ＝⟨ Ⅰ ⟩
                           x ∧ (y ∧ y) ＝⟨ Ⅱ ⟩
                           x ∧ y ∎
                            where
                             Ⅰ = ∧-associative x y y ⁻¹
                             Ⅱ = ap (x ∧_) (∧-idempotent y)

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

 ∧-absorptive₁ : (x y : X) → x ∧ (y ∨ x) ＝ x
 ∧-absorptive₁ x y = x ∧ (y ∨ x) ＝⟨ ap (x ∧_) (∨-commutative y x) ⟩
                     x ∧ (x ∨ y) ＝⟨ ∧-absorptive x y              ⟩
                     x           ∎

 ∧-absorptive₃ : (x y : X) → (y ∨ x) ∧ x ＝ x
 ∧-absorptive₃ x y = (y ∨ x) ∧ x ＝⟨ ∧-commutative (y ∨ x) x ⟩
                     x ∧ (y ∨ x) ＝⟨ ∧-absorptive₁ x y ⟩
                     x           ∎

 ∨-absorptive₁ : (x y : X) → (x ∧ y) ∨ x ＝ x
 ∨-absorptive₁ x y = (x ∧ y) ∨ x ＝⟨ ∨-commutative (x ∧ y) x ⟩
                     x ∨ (x ∧ y) ＝⟨ ∨-absorptive x y        ⟩
                     x           ∎

 ∨-absorptive₂ : (x y : X) → (y ∧ x) ∨ x ＝ x
 ∨-absorptive₂ x y = (y ∧ x) ∨ x ＝⟨ Ⅰ ⟩
                     (x ∧ y) ∨ x ＝⟨ Ⅱ ⟩
                     x           ∎
                      where
                       Ⅰ = ap (_∨ x) (∧-commutative y x)
                       Ⅱ = ∨-absorptive₁ x y

 ∨-absorptive₃ : (x y : X) → x ∨ (y ∧ x) ＝ x
 ∨-absorptive₃ x y = x ∨ (y ∧ x)   ＝⟨ ∨-commutative x (y ∧ x) ⟩
                     (y ∧ x) ∨ x   ＝⟨ ∨-absorptive₂ x y       ⟩
                     x             ∎

 distributivity-op : (x y z : X) → x ∨ (y ∧ z) ＝ (x ∨ y) ∧ (x ∨ z)
 distributivity-op x y z =
  x ∨ (y ∧ z)                      ＝⟨ Ⅰ ⟩
  x ∨ ((z ∧ y) ∨ (z ∧ x))          ＝⟨ Ⅱ ⟩
  ((x ∨ y) ∧ z) ∨ ((x ∨ y) ∧ z)    ＝⟨ Ⅲ ⟩
  (x ∨ y) ∧ (x ∨ z)                ∎
   where
    p = ap (_∨ (y ∧ z)) (∨-absorptive₃ x z ⁻¹)
    q = ap ((x ∨ (z ∧ x)) ∨_) (∧-commutative y z)
    r = ∨-associative x (z ∧ x) (z ∧ y) ⁻¹
    s = ap (x ∨_) (∨-commutative (z ∧ x) (z ∧ y))

    Ⅰ = x ∨ (y ∧ z)               ＝⟨ p ⟩
        (x ∨ (z ∧ x)) ∨ (y ∧ z)   ＝⟨ q ⟩
        (x ∨ (z ∧ x)) ∨ (z ∧ y)   ＝⟨ r ⟩
        x ∨ ((z ∧ x) ∨ (z ∧ y))   ＝⟨ s ⟩
        x ∨ ((z ∧ y) ∨ (z ∧ x))   ∎
    Ⅱ = x ∨ ((z ∧ y) ∨ (z ∧ x))       ＝⟨ {!!} ⟩
        x ∨ (z ∧ (y ∨ x))             ＝⟨ {!!} ⟩
        ((x ∨ y) ∧ z) ∨ ((x ∨ y) ∧ z) ∎
    Ⅲ = {!!}

\end{code}

\begin{code}

∣_∣ᵈ : DistributiveLattice 𝓤 → 𝓤  ̇
∣_∣ᵈ L = let open DistributiveLattice L in X

\end{code}

\begin{code}

orderᵈ : (L : DistributiveLattice 𝓤)
       → ∣ L ∣ᵈ → ∣ L ∣ᵈ → Ω 𝓤
orderᵈ L x y = (x ∧ y ＝ x) , X-is-set
 where
  open DistributiveLattice L

syntax orderᵈ L x y = x ≤ᵈ[ L ] y

≤ᵈ-is-reflexive : (L : DistributiveLattice 𝓤) → is-reflexive (orderᵈ L) holds
≤ᵈ-is-reflexive L = ∧-idempotent
 where
  open DistributiveLattice L

≤ᵈ-is-transitive : (L : DistributiveLattice 𝓤) → is-transitive (orderᵈ L) holds
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

≤ᵈ-is-antisymmetric : (L : DistributiveLattice 𝓤) → is-antisymmetric (orderᵈ L)
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

orderᵈ-∨ : (L : DistributiveLattice 𝓤) → ∣ L ∣ᵈ → ∣ L ∣ᵈ → Ω 𝓤
orderᵈ-∨ L x y = (x ∨ y ＝ y) , X-is-set
 where
  open DistributiveLattice L

orderᵈ-∨-implies-orderᵈ : (L : DistributiveLattice 𝓤) {x y : ∣ L ∣ᵈ}
                        → (orderᵈ-∨ L x y ⇒ orderᵈ L x y) holds
orderᵈ-∨-implies-orderᵈ L {x} {y} p =
 x ∧ y ＝⟨ Ⅰ ⟩ x ∧ (x ∨ y) ＝⟨ Ⅱ ⟩ x ∎
  where
   open DistributiveLattice L

   Ⅰ = ap (x ∧_) p ⁻¹
   Ⅱ = ∧-absorptive x y

orderᵈ-implies-orderᵈ-∨ : (L : DistributiveLattice 𝓤) {x y : ∣ L ∣ᵈ}
                        → (orderᵈ L x y ⇒ orderᵈ-∨ L x y) holds
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

\begin{code}

poset-ofᵈ : DistributiveLattice 𝓤 → Poset 𝓤 𝓤
poset-ofᵈ L = ∣ L ∣ᵈ
            , orderᵈ L
            , (≤ᵈ-is-reflexive L , ≤ᵈ-is-transitive L)
            , ≤ᵈ-is-antisymmetric L
 where
  open DistributiveLattice L

\end{code}

\begin{code}

module _ (L : DistributiveLattice 𝓤) where

 open DistributiveLattice L
 open Meets (orderᵈ L)

 ∧-is-greatest : (x y z : ∣ L ∣ᵈ)
               → (z is-a-lower-bound-of (x , y) ⇒ z ≤ (x ∧ y)) holds
 ∧-is-greatest x y z (p₁ , p₂) = †
  where
   p₁′ : z ∨ x ＝ x
   p₁′ = orderᵈ-implies-orderᵈ-∨ L p₁

   p₂′ : z ∨ y ＝ y
   p₂′ = orderᵈ-implies-orderᵈ-∨ L p₂

   † : orderᵈ L z (x ∧ y) holds
   † = z ∧ (x ∧ y)                   ＝⟨ Ⅰ ⟩
       z ∧ ((z ∨ x) ∧ y)             ＝⟨ Ⅱ ⟩
       z ∧ ((z ∧ y) ∨ (x ∧ y))       ＝⟨ Ⅲ ⟩
       (z ∧ (z ∧ y)) ∨ (z ∧ (x ∧ y)) ＝⟨ {!!} ⟩
       z ∨ (z ∧ y)                   ＝⟨ Ⅳ ⟩
       z                             ∎
        where
         Ⅰ = ap (λ - → z ∧ (- ∧ y)) (p₁′ ⁻¹)
         Ⅱ = ap (z ∧_) (distributivityᵈ₁ y z x)
         Ⅲ = distributivityᵈ z (z ∧ y) (x ∧ y)
         -- Ⅲ = ap (_∨ (z ∧ y)) (∧-absorptive z x)
         Ⅳ = ∨-absorptive z y

 ∧-is-glb : (x y : ∣ L ∣ᵈ) → ((x ∧ y) is-glb-of (x , y)) holds
 ∧-is-glb x y = (∧-is-a-lower-bound₁ x y , ∧-is-a-lower-bound₂ x y)
              , λ (z , p) → ∧-is-greatest x y z p

\end{code}
