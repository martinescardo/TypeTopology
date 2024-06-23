---
title:          Definition of distributive lattices (Σ-based)
author:         Ayberk Tosun
date-started:   2024-05-16
date-completed: 2024-05-17
dates-updated:  [2024-06-01]
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets

module Locales.DistributiveLattice.Definition-SigmaBased
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open import Locales.DistributiveLattice.Definition fe pt
open import Locales.Frame pt fe
open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier

open Implication fe

\end{code}

Sigma-based definition of distributive lattices.

\begin{code}

Distributive-Lattice-Data : 𝓤  ̇ → 𝓤  ̇
Distributive-Lattice-Data A = A           -- bottom element
                            × A           -- top element
                            × (A → A → A) -- binary meet
                            × (A → A → A) -- binary join

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)

satisfies-distributive-lattice-laws₀
 : {A : 𝓤  ̇}
 → is-set A
 → Distributive-Lattice-Data A
 → Ω 𝓤
satisfies-distributive-lattice-laws₀ {𝓤} {A} s (𝟎 , 𝟏 , _∧_ , _∨_) =
 let
  open Equality s
 in
     (Ɐ x y z ꞉ A , x ∧ (y ∧ z) ＝ₚ (x ∧ y) ∧ z)
  ∧ₚ (Ɐ x y ꞉ A , x ∧ y ＝ₚ y ∧ x)
  ∧ₚ (Ɐ x ꞉ A , x ∧ 𝟏 ＝ₚ x)
  ∧ₚ (Ɐ x ꞉ A , x ∧ x ＝ₚ x)
  ∧ₚ (Ɐ x y ꞉ A , x ∧ (x ∨ y) ＝ₚ x)
  ∧ₚ (Ɐ x y z ꞉ A , x ∨ (y ∨ z) ＝ₚ (x ∨ y) ∨ z)
  ∧ₚ (Ɐ x y ꞉ A , x ∨ y ＝ₚ y ∨ x)
  ∧ₚ (Ɐ x ꞉ A , x ∨ 𝟎 ＝ₚ x)
  ∧ₚ (Ɐ x ꞉ A , x ∨ x ＝ₚ x)
  ∧ₚ (Ɐ x y ꞉ A , x ∨ (x ∧ y) ＝ₚ x)
  ∧ₚ (Ɐ x y z ꞉ A , x ∧ (y ∨ z) ＝ₚ (x ∧ y) ∨ (x ∧ z))

satisfies-distributive-lattice-laws
 : {A : 𝓤  ̇} → Distributive-Lattice-Data A → 𝓤  ̇
satisfies-distributive-lattice-laws {𝓤} {A} d =
 Σ s ꞉ is-set A , satisfies-distributive-lattice-laws₀ s d holds

\end{code}

Added on 2024-06-01.

\begin{code}

satisfying-distributive-lattice-laws-is-prop
 : {A : 𝓤  ̇}
 → (d : Distributive-Lattice-Data A)
 → is-prop (satisfies-distributive-lattice-laws d)
satisfying-distributive-lattice-laws-is-prop d =
 Σ-is-prop
  (being-set-is-prop fe)
  (λ s → holds-is-prop (satisfies-distributive-lattice-laws₀ s d))

\end{code}

End of addition.

\begin{code}

Distributive-Lattice-Structure : (A : 𝓤  ̇) → 𝓤  ̇
Distributive-Lattice-Structure A =
 Σ d ꞉ Distributive-Lattice-Data A , satisfies-distributive-lattice-laws d

\end{code}

We denote the Σ-based version of the type of distributive lattices by
`Distributive-Lattice₀` to distinguish it from the record-based version.

\begin{code}

Distributive-Lattice₀ : (𝓤 : Universe) → 𝓤 ⁺  ̇
Distributive-Lattice₀ 𝓤 = Σ A ꞉ 𝓤  ̇ , Distributive-Lattice-Structure A

\end{code}

Notation for the underlying distributive lattice data.

\begin{code}

distributive-lattice-data-of : (A : 𝓤  ̇)
                             → Distributive-Lattice-Structure A
                             → Distributive-Lattice-Data A
distributive-lattice-data-of A (str , _) = str

\end{code}

We now prove that this type is equivalent to the record-based version.

We first define the map going from the Σ-based definition to the record-based
definition.

\begin{code}

to-distributive-lattice : (𝓤 : Universe)
                        → Distributive-Lattice₀ 𝓤
                        → DistributiveLattice 𝓤
to-distributive-lattice 𝓤 (X , ((𝟎 , 𝟏 , _∧_ , _∨_) , laws)) =
 let
  (X-is-set     , rest) = laws
  (∧-assoc      , rest) = rest
  (∧-comm       , rest) = rest
  (∧-unit       , rest) = rest
  (∧-idempotent , rest) = rest
  (∧-absorptive , rest) = rest
  (∨-assoc      , rest) = rest
  (∨-comm       , rest) = rest
  (∨-unit       , rest) = rest
  (∨-idempotent , rest) = rest
  (∨-absorptive , rest) = rest
  distributivity        = rest
 in
  record
   { X               = X
   ; 𝟏               = 𝟏
   ; 𝟎               = 𝟎
   ; _∧_             = _∧_
   ; _∨_             = _∨_
   ; X-is-set        = X-is-set
   ; ∧-associative   = ∧-assoc
   ; ∧-commutative   = ∧-comm
   ; ∧-unit          = ∧-unit
   ; ∧-idempotent    = ∧-idempotent
   ; ∧-absorptive    = ∧-absorptive
   ; ∨-associative   = ∨-assoc
   ; ∨-commutative   = ∨-comm
   ; ∨-unit          = ∨-unit
   ; ∨-idempotent    = ∨-idempotent
   ; ∨-absorptive    = ∨-absorptive
   ; distributivityᵈ = distributivity
   }

\end{code}

Now the map going from the record-based definition to the Σ-based one.

\begin{code}

to-distributive-lattice₀ : (𝓤 : Universe)
                         → DistributiveLattice 𝓤
                         → Distributive-Lattice₀ 𝓤
to-distributive-lattice₀ 𝓤 L = X , d , †
 where
  open DistributiveLattice L

  d : Distributive-Lattice-Data X
  d = 𝟎 , 𝟏 , _∧_ , _∨_

  † : satisfies-distributive-lattice-laws d
  † = X-is-set
    , ∧-associative
    , ∧-commutative
    , ∧-unit
    , ∧-idempotent
    , ∧-absorptive
    , ∨-associative
    , ∨-commutative
    , ∨-unit
    , ∨-idempotent
    , ∨-absorptive
    , distributivityᵈ

\end{code}

We now prove that these two maps form an equivalence, which follows trivially
from the definitional equality.

\begin{code}

distributive-lattice₀-equivalent-to-distributive-lattice
 : (𝓤 : Universe)
 → Distributive-Lattice₀ 𝓤 ≃ DistributiveLattice 𝓤
distributive-lattice₀-equivalent-to-distributive-lattice 𝓤 =
 to-distributive-lattice 𝓤 , qinvs-are-equivs (to-distributive-lattice 𝓤) †
  where
   † : qinv (to-distributive-lattice 𝓤)
   † = to-distributive-lattice₀ 𝓤 , (λ _ → refl) , (λ _ → refl)

\end{code}

Added on 2024-06-01.

The types of distributive lattice data and distributive lattice structure are
sets.

\begin{code}

distributive-lattice-data-is-set
 : (A : 𝓤  ̇)
 → is-set A
 → propext 𝓤
 → is-set (Distributive-Lattice-Data A)
distributive-lattice-data-is-set A σ pe =
 ×-is-set σ (×-is-set σ (×-is-set † †))
  where
   † : is-set (A → A → A)
   † = Π-is-set fe λ _ → Π-is-set fe λ _ → σ

distributive-lattice-structure-is-set
 : (A : 𝓤  ̇)
 → propext 𝓤
 → is-set (Distributive-Lattice-Structure A)
distributive-lattice-structure-is-set A pe {str₁} {str₂} =
 Σ-is-set (distributive-lattice-data-is-set A σ pe) †
  where
   σ : is-set A
   σ = DistributiveLattice.X-is-set (to-distributive-lattice _ (A , str₁))

   † : (d : Distributive-Lattice-Data A)
     → is-set (satisfies-distributive-lattice-laws d)
   † d = props-are-sets (satisfying-distributive-lattice-laws-is-prop d)

\end{code}

End of addition.
