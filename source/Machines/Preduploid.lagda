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
open import Categories.Precategory

module _ (𝓓 : deductive-system 𝓤 𝓥) where
 open deductive-system 𝓓
 open ⊢-properties 𝓓
 open polarities 𝓓

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

preduploid : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
preduploid 𝓤 𝓥 =  Σ 𝓓 ꞉ deductive-system 𝓤 𝓥 , preduploid-axioms 𝓓

module preduploid (𝓓 : preduploid 𝓤 𝓥) where

 underlying-deductive-system : deductive-system 𝓤 𝓥
 underlying-deductive-system = pr₁ 𝓓

 open deductive-system underlying-deductive-system public

 ob-is-polarized : (A : ob) → is-polarized underlying-deductive-system A
 ob-is-polarized = pr₂ 𝓓

module depolarization (𝓓 : deductive-system 𝓤 𝓥) where
  open deductive-system 𝓓
  open ⊢-properties 𝓓
  open polarities 𝓓

  depolarization : 𝓤 ⊔ 𝓥 ̇
  depolarization = ((A : ob) → is-positive A) + ((A : ob) → is-negative A)

  is-depolarized : 𝓤 ⊔ 𝓥 ̇
  is-depolarized = ∥ depolarization ∥

  module depolarization-gives-precategory (depol : is-depolarized) where
   assoc : category-axiom-statements.statement-assoc (pr₁ 𝓓)
   assoc A B C D f g h = ∥∥-rec (⊢-is-set A D) assoc-case depol
    where
     assoc-case : depolarization → cut f (cut g h) ＝ cut (cut f g) h
     assoc-case (inl pos) = pos C D h A B g f ⁻¹
     assoc-case (inr neg) = neg B A f C D g h ⁻¹

   main : precategory-axioms (pr₁ 𝓓)
   pr₁ main = ⊢-is-set
   pr₁ (pr₂ main) = idn-L
   pr₁ (pr₂ (pr₂ main)) = idn-R
   pr₂ (pr₂ (pr₂ main)) = assoc

\end{code}
