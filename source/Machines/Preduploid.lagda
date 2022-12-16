Jon Sterling, started 27th Sep 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF.PropTrunc

module Machines.Preduploid (pt : propositional-truncations-exist) where

open PropositionalTruncation pt

open import MLTT.Spartan
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import Machines.DeductiveSystem

module _ {𝓤 𝓥} (𝓓 : deductive-system 𝓤 𝓥) where
 open deductive-system 𝓓

 is-polarized : (A : ob) → 𝓤 ⊔ 𝓥 ̇
 is-polarized A = ∥ is-positive A + is-negative A ∥

 is-polarized-is-prop : {A : ob} → is-prop (is-polarized A)
 is-polarized-is-prop = ∥∥-is-prop

 preduploid-axioms : 𝓤 ⊔ 𝓥 ̇
 preduploid-axioms = (A : ob) → is-polarized A

 module _ (fe : funext 𝓤 (𝓤 ⊔ 𝓥)) where
  preduploid-axioms-is-prop : is-prop preduploid-axioms
  preduploid-axioms-is-prop =
   Π-is-prop fe λ _ →
   is-polarized-is-prop

module _ (𝓤 𝓥 : Universe) where
 preduploid : (𝓤 ⊔ 𝓥) ⁺ ̇
 preduploid = Σ 𝓓 ꞉ deductive-system 𝓤 𝓥 , preduploid-axioms 𝓓

\end{code}
