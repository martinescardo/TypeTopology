Tom de Jong, July 2024.

This file corresponds to the paper

   "Domain Theory in Univalent Foundations I:
    Directed complete posets and Scott’s D∞"
   Tom de Jong
   2024
   https://arxiv.org/abs/TODO

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.Subsingletons
open import UF.PropTrunc

module DomainTheory.Part-I
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import MLTT.Spartan

open import UF.Powerset-MultiUniverse
open import UF.Sets
open import UF.Size
open import UF.SubtypeClassifier

open import OrderedTypes.Poset fe
{-

open import DomainTheory.Basics.Exponential     -- (2)
open import DomainTheory.Basics.LeastFixedPoint -- (3)
open import DomainTheory.Basics.Miscelanea      -- (4)
open import DomainTheory.Basics.Pointed         -- (5)
open import DomainTheory.Basics.SupComplete     -- (6)
open import DomainTheory.Basics.WayBelow        -- (7)

open import DomainTheory.BasesAndContinuity.Bases                   -- (1)
open import DomainTheory.BasesAndContinuity.CompactBasis            -- (2)
open import DomainTheory.BasesAndContinuity.Continuity              -- (3)
open import DomainTheory.BasesAndContinuity.ContinuityDiscussion    -- (4)
open import DomainTheory.BasesAndContinuity.ContinuityImpredicative -- (5)
open import DomainTheory.BasesAndContinuity.IndCompletion           -- (6)
open import DomainTheory.BasesAndContinuity.StepFunctions           -- (7)

open import DomainTheory.Bilimits.Directed   -- (1)
open import DomainTheory.Bilimits.Sequential -- (2)
open import DomainTheory.Bilimits.Dinfinity  -- (3)

open import DomainTheory.Examples.IdlDyadics              -- (1)
open import DomainTheory.Examples.LiftingLargeProposition -- (2)
open import DomainTheory.Examples.Omega                   -- (3)
open import DomainTheory.Examples.Ordinals                -- (4)
open import DomainTheory.Examples.Powerset                -- (5)

open import DomainTheory.IdealCompletion.IdealCompletion -- (1)
open import DomainTheory.IdealCompletion.Properties      -- (2)
open import DomainTheory.IdealCompletion.Retracts        -- (3)

open import DomainTheory.Lifting.LiftingDcpo         -- (1)
open import DomainTheory.Lifting.LiftingSet          -- (2)
open import DomainTheory.Lifting.LiftingSetAlgebraic -- (3)

open import DomainTheory.Taboos.ClassicalLiftingOfNaturalNumbers
-}

-- open import DomainTheory.Lifting.*

-- Section 2

Definition-2-1 : (𝓤 : Universe) (X : 𝓥 ̇  ) → 𝓤 ⁺ ⊔ 𝓥 ̇
Definition-2-1 𝓤 X = X is 𝓤 small

Definition-2-2 : (𝓤 : Universe) → 𝓤 ⁺ ̇
Definition-2-2 𝓤 = Ω 𝓤

Definition-2-3 : (𝓥 : Universe) (X : 𝓤 ̇  ) → 𝓥 ⁺ ⊔ 𝓤 ̇
Definition-2-3 𝓥 X = 𝓟 {𝓥} X

Definition-2-4 : (𝓥 : Universe) (X : 𝓤 ̇  )
               → (X → 𝓟 {𝓥} X → 𝓥 ̇  )
               × (𝓟 {𝓥} X → 𝓟 {𝓥} X → 𝓥 ⊔ 𝓤 ̇  )
Definition-2-4 𝓥 X = _∈_ , _⊆_

-- Section 3

module _
        (P : 𝓤 ̇  ) (_⊑_ : P → P → 𝓣 ̇  )
       where

 open PosetAxioms

 Definition-3-1 : 𝓤 ⊔ 𝓣 ̇
 Definition-3-1 = is-prop-valued _⊑_
                × is-reflexive _⊑_
                × is-transitive _⊑_

 Definition-3-2 : 𝓤 ⊔ 𝓣 ̇
 Definition-3-2 = Definition-3-1 × is-antisymmetric _⊑_

 Lemma-3-3 : is-prop-valued _⊑_
           → is-reflexive _⊑_
           → is-antisymmetric _⊑_
           → is-set P
 Lemma-3-3 = posets-are-sets _⊑_

 module _ (𝓥 : Universe) where
  open import DomainTheory.Basics.Dcpo pt fe 𝓥

  Definition-3-4 : {I : 𝓥 ̇  } → (I → P) → (𝓥 ⊔ 𝓣 ̇  ) × (𝓥 ⊔ 𝓣 ̇  )
  Definition-3-4 {I} α = is-semidirected _⊑_ α , is-directed _⊑_ α

  Remark-3-5 : {I : 𝓥 ̇  } (α : I → P)
             → is-directed _⊑_ α
             ＝ ∥ I ∥ × ((i j : I) → ∥ Σ k ꞉ I , (α i ⊑ α k) × (α j ⊑ α k) ∥)
  Remark-3-5 α = refl

  Definition-3-6 : {I : 𝓥 ̇  } → P → (I → P) → (𝓥 ⊔ 𝓣 ̇  ) × (𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇  )
  Definition-3-6 {I} x α = (is-upperbound _⊑_ x α) , is-sup _⊑_ x α

  Definition-3-6-ad : poset-axioms _⊑_
                    → {I : 𝓥 ̇  } (α : I → P)
                    → {x y : P} → is-sup _⊑_ x α → is-sup _⊑_ y α → x ＝ y
  Definition-3-6-ad pa {I} α = sups-are-unique _⊑_ pa α

  Definition-3-7 : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  Definition-3-7 = is-directed-complete _⊑_

  Definition-3-7-ad : (𝓓 : DCPO {𝓤} {𝓣}) {I : 𝓥 ̇}
                      {α : I → ⟨ 𝓓 ⟩} → is-Directed 𝓓 α → ⟨ 𝓓 ⟩
  Definition-3-7-ad = ∐

  Remark-3-8 : {!!}
  Remark-3-8 = {!!}

  Definition-3-9 : {𝓤 𝓣 : Universe} → (𝓤 ⊔ 𝓥 ⊔ 𝓣) ⁺ ̇
  Definition-3-9 {𝓤} {𝓣} = DCPO {𝓤} {𝓣}

\end{code}