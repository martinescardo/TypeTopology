Tom de Jong, 5 November 2025.

We give the standard definition of metric spaces using the Dedekind reals, as
opposed to the alternative definition developed by Andrew Sneap in
MetricSpaces.Type.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module MetricSpaces.StandardDefinition
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import MLTT.Spartan
open import UF.HedbergApplications
open import UF.Sets
open import UF.Subsingletons-FunExt

open import DedekindReals.Addition fe pe pt
 renaming (_+_ to _+ℝ_) hiding (_-_)
open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt

module _
        (M : 𝓤 ̇ )
        (d : M → M → ℝ)
       where

 reflexivity : 𝓤₁ ⊔ 𝓤 ̇
 reflexivity = (x y : M) → d x y ＝ 0ℝ ↔ x ＝ y

 symmetry : 𝓤₁ ⊔ 𝓤 ̇
 symmetry = (x y : M) → d x y ＝ d y x

 triangle-inequality : 𝓤 ̇
 triangle-inequality = (x y z : M) → d x y +ℝ d y z ≤ℝ d x z

 metric-axioms : 𝓤₁ ⊔ 𝓤 ̇
 metric-axioms = reflexivity × symmetry × triangle-inequality

 metric-space-is-set : reflexivity → is-set M
 metric-space-is-set ρ =
  reflexive-prop-valued-relation-that-implies-equality-gives-set
   (λ x y → d x y ＝ 0ℝ)
   (λ x y → ℝ-is-set)
   (λ x → rl-implication (ρ x x) refl)
   (λ x y → lr-implication (ρ x y))

 metric-axioms-is-prop : is-prop metric-axioms
 metric-axioms-is-prop =
  ×₃-is-prop I II III
   where
    I : is-prop reflexivity
    I = prop-criterion
         (λ ρ → Π₂-is-prop fe
                 (λ _ _ → ×-is-prop
                   (Π-is-prop fe (λ _ → metric-space-is-set ρ))
                   (Π-is-prop fe (λ _ → ℝ-is-set))))
    II : is-prop symmetry
    II = Π₂-is-prop fe (λ _ _ → ℝ-is-set)
    III : is-prop triangle-inequality
    III = Π₃-is-prop fe (λ x y z → ≤-is-prop (d x y +ℝ d y z) (d x z))

Metric-Space : (𝓤 : Universe) → 𝓤₁ ⊔ 𝓤 ⁺ ̇
Metric-Space 𝓤 = Σ M ꞉ 𝓤 ̇  , Σ d ꞉ (M → M → ℝ) , metric-axioms M d

\end{code}