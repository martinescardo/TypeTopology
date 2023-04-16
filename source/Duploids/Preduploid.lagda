Jon Sterling, started 16th Dec 2022

A preduploid is a deductive system in which every object is polarized,
i.e. either positive or negative. Because an object could be both positive *and*
negative, it is necessary to state the preduploid axiom using a propositional
truncation. This definition differs from that of Munch-Maccagnoni (who includes
in the definition of a preduploid a choice of polarization), who has suggested
the modified definition in private communication.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import UF.PropTrunc
open import UF.FunExt

module Duploids.Preduploid (fe : Fun-Ext) (pt : propositional-truncations-exist) where

open PropositionalTruncation pt

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.Retracts
open import UF.hlevels
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import Categories.Category fe
open import Duploids.DeductiveSystem fe

module _ (𝓓 : deductive-system-structure 𝓤 𝓥) where
 open deductive-system-structure 𝓓
 open ⊢-properties 𝓓

 is-polarized : (A : ob) → 𝓤 ⊔ 𝓥 ̇
 is-polarized A = ∥ is-positive A + is-negative A ∥

 being-polarized-is-prop : {A : ob} → is-prop (is-polarized A)
 being-polarized-is-prop = ∥∥-is-prop

 preduploid-axioms : 𝓤 ⊔ 𝓥 ̇
 preduploid-axioms = deductive-system-axioms 𝓓 × ((A : ob) → is-polarized A)

 preduploid-axioms-is-prop : is-prop preduploid-axioms
 preduploid-axioms-is-prop =
  ×-is-prop
   (deductive-system-axioms-is-prop 𝓓)
   (Π-is-prop fe λ _ →
    being-polarized-is-prop)

record preduploid (𝓤 𝓥 : Universe) : (𝓤 ⊔ 𝓥)⁺ ̇ where
 constructor make
 field
  ob : 𝓤 ̇
  _⊢_ : ob → ob → 𝓥 ̇
  idn : (A : ob) → A ⊢ A
  cut' : (A B C : ob) (f : A ⊢ B) (g : B ⊢ C) → A ⊢ C

 cut : {A B C : ob} (f : A ⊢ B) (g : B ⊢ C) → A ⊢ C
 cut = cut' _ _ _

 str : deductive-system-structure 𝓤 𝓥
 str = ob , _⊢_ , idn , cut'

 field
  ax : preduploid-axioms str

 underlying-deductive-system : deductive-system 𝓤 𝓥
 underlying-deductive-system = make ob _⊢_ idn cut' (pr₁ ax)

 ob-is-polarized = pr₂ ax
 open ⊢-properties str public

 open deductive-system-axioms str (pr₁ ax) public

module preduploid-as-sum (𝓤 𝓥 : Universe) where
 to-sum : preduploid 𝓤 𝓥 → Σ str ꞉ deductive-system-structure 𝓤 𝓥 , preduploid-axioms str
 to-sum 𝓓 = let open preduploid 𝓓 in str , ax

 module _ (𝓓 : (Σ str ꞉ deductive-system-structure 𝓤 𝓥 , preduploid-axioms str)) where
  private
   str = pr₁ 𝓓
   ax = pr₂ 𝓓
   module str = deductive-system-structure str

  from-sum : preduploid 𝓤 𝓥
  preduploid.ob from-sum = str.ob
  preduploid._⊢_ from-sum = str._⊢_
  preduploid.idn from-sum = str.idn
  preduploid.cut' from-sum _ _ _ = str.cut
  preduploid.ax from-sum = ax

 to-sum-is-equiv : is-equiv to-sum
 pr₁ (pr₁ to-sum-is-equiv) = from-sum
 pr₂ (pr₁ to-sum-is-equiv) _ = refl
 pr₁ (pr₂ to-sum-is-equiv) = from-sum
 pr₂ (pr₂ to-sum-is-equiv) _ = refl

 equiv : preduploid 𝓤 𝓥 ≃ (Σ str ꞉ deductive-system-structure 𝓤 𝓥 , preduploid-axioms str)
 equiv = to-sum , to-sum-is-equiv

module preduploid-extras (𝓓 : preduploid 𝓤 𝓥) where
 open deductive-system-extras (preduploid.underlying-deductive-system 𝓓) public
\end{code}
