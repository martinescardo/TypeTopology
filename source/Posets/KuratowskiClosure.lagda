A Kuratowski closure operator is a closure operator that preserves joins.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import Posets.JoinSemiLattices

module Posets.KuratowskiClosure
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where
open import Posets.Poset fe
open import Posets.Closure fe pt

module _ (D : JoinSemiLattice 𝓥 𝓣) where
  open JoinSemiLattice D
  open MonotoneAxioms _⊑_ _⊑_
  open Closure _⊑_

  kuratowski-closure-axioms : (L → L) → _
  kuratowski-closure-axioms f
    = is-monotone f
    × (closure-η f × closure-μ f)
    × (preserves-⊥ × preserves-∨)
   where
    preserves-⊥ = f ⊥ ＝ ⊥
    preserves-∨ = ∀ x y → f (x ∨ y) ＝ f x ∨ f y

\end{code}
