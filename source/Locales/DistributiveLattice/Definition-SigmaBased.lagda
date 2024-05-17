--------------------------------------------------------------------------------
title:          Definition of distributive lattices (Σ-based)
author:         Ayberk Tosun
date-started:   2024-05-16
date-completed: 2024-05-17
--------------------------------------------------------------------------------

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
open import UF.SubtypeClassifier

open Implication fe

\end{code}

Sigma-based definition of distributive lattices.

\begin{code}

Distributive-Lattice-Data : 𝓤  ̇ → 𝓤  ̇
Distributive-Lattice-Data A = A           -- top element
                            × A           -- bottom element
                            × (A → A → A) -- binary meet
                            × (A → A → A) -- binary join

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)

satisfies-distributive-lattice-laws
 : {A : 𝓤  ̇} → Distributive-Lattice-Data A → 𝓤  ̇
satisfies-distributive-lattice-laws {𝓤} {A} (𝟎 , 𝟏 , _∧_ , _∨_) =
 Σ s ꞉ is-set A , rest s holds
  where

   rest : is-set A → Ω 𝓤
   rest s =  (Ɐ x y z ꞉ A , x ∧ (y ∧ z) ＝ₚ (x ∧ y) ∧ z)
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
    where
     open Equality s

\end{code}

\begin{code}

Distributive-Lattice-Structure : (A : 𝓤  ̇) → 𝓤  ̇
Distributive-Lattice-Structure A =
 Σ d ꞉ Distributive-Lattice-Data A , satisfies-distributive-lattice-laws d

\end{code}

We denote the type Σ-version of the type of distributive lattices
`Distributive-Lattice₀` to distinguish it from the record-based version.

\begin{code}

Distributive-Lattice₀ : (𝓤 : Universe) → 𝓤 ⁺  ̇
Distributive-Lattice₀ 𝓤 = Σ A ꞉ 𝓤  ̇ , Distributive-Lattice-Structure A

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
