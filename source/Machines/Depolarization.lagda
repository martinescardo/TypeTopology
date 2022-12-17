Jon Sterling, started 17th Dec 2022

We could consider three forms of depolarization for a deductive system:
1. All objects have positive polarity
2. All objects have negative polarity
3. Either (1) or (2).

It will happen that all three forms of depolarization are equivalent; moreover,
a depolarized deductive system is the same thing as a precategory.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan

module Machines.Depolarization where

open import UF.FunExt
open import UF.Base
open import UF.Equiv
open import UF.PropTrunc
open import UF.Retracts
open import UF.hlevels
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Lower-FunExt

open import Categories.Category
open import Machines.DeductiveSystem

module _ (𝓓 : deductive-system 𝓤 𝓥) where
 open deductive-system 𝓓
 open polarities 𝓓

 is-pos-depolarized : 𝓤 ⊔ 𝓥 ̇
 is-pos-depolarized = (A : ob) → is-positive A

 is-neg-depolarized : 𝓤 ⊔ 𝓥 ̇
 is-neg-depolarized = (A : ob) → is-negative A

 module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥)) (fe1 : funext 𝓥 (𝓤 ⊔ 𝓥)) where
  being-pos-depolarized-is-prop : is-prop is-pos-depolarized
  being-pos-depolarized-is-prop =
   Π-is-prop fe0 λ _ →
   being-positive-is-prop fe0 fe1

  being-neg-depolarized-is-prop : is-prop is-neg-depolarized
  being-neg-depolarized-is-prop =
   Π-is-prop fe0 λ _ →
   being-negative-is-prop fe0 fe1

 -- The positive and negative depolarizations are equivalent:
 is-pos-depolarized-gives-is-neg-depolarized
  : is-pos-depolarized
  → is-neg-depolarized
 is-pos-depolarized-gives-is-neg-depolarized pos A B f C D g h =
  pos C D h B A g f

 is-neg-depolarized-gives-is-pos-depolarized
  : is-neg-depolarized
  → is-pos-depolarized
 is-neg-depolarized-gives-is-pos-depolarized neg A B f U V g h =
  neg V U h A B g f

 -- A depolarized deductive system enjoys the full associativity axiom
 -- and therefore gives rise to a precategory.
 module depolarization-and-precategories (H : is-pos-depolarized) where
  depolarization-gives-assoc : category-axiom-statements.statement-assoc (pr₁ 𝓓)
  depolarization-gives-assoc A B C D f g h = H C D h A B g f ⁻¹

  depolarization-gives-precategory-axioms : precategory-axioms (pr₁ 𝓓)
  depolarization-gives-precategory-axioms =
   ⊢-is-set ,
   idn-L ,
   idn-R ,
   depolarization-gives-assoc

  precategory-of-depolarized-deductive-system : precategory 𝓤 𝓥
  precategory-of-depolarized-deductive-system =
   pr₁ 𝓓 ,
   depolarization-gives-precategory-axioms

  -- Conversely, any deductive system enjoying the axioms of a precategory is
  -- depolarized.
 module _ (ax : precategory-axioms (pr₁ 𝓓)) where
  module ax = precategory-axioms (pr₁ 𝓓) ax

  precategory-gives-pos-depolarized : is-pos-depolarized
  precategory-gives-pos-depolarized A B f U V g h =
   ax.assoc U V A B h g f ⁻¹



 -- For the sake of symmetry, we may considered an equivalent "unbiased" form
 -- of depolarization, which requires propositional truncation.

 module unbiased-depolarization (pt : propositional-truncations-exist) where
  open PropositionalTruncation pt

  depolarization : 𝓤 ⊔ 𝓥 ̇
  depolarization = is-pos-depolarized + is-neg-depolarized

  is-depolarized : 𝓤 ⊔ 𝓥 ̇
  is-depolarized = ∥ depolarization ∥

  -- When a deductive system is depolarized in the unbiased sense,
  -- it is both positively and negatively depolarized. Hence, all notions
  -- of depolarization are equivalent.

  module _ (H : is-depolarized) where
   is-depolarized-gives-is-pos-depolarized : is-pos-depolarized
   is-depolarized-gives-is-pos-depolarized A B f U V g h =
    ∥∥-rec (⊢-is-set _ _) case H
    where
     case : depolarization → cut (cut h g) f ＝ cut h (cut g f)
     case (inl pos) =
      pos A B f U V g h
     case (inr neg) =
      is-neg-depolarized-gives-is-pos-depolarized
       neg
       A B f U V g h

   is-depolarized-gives-is-neg-depolarized : is-neg-depolarized
   is-depolarized-gives-is-neg-depolarized =
    is-pos-depolarized-gives-is-neg-depolarized
     is-depolarized-gives-is-pos-depolarized


depolarized-deductive-system : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
depolarized-deductive-system 𝓤 𝓥 =
 Σ 𝓓 ꞉ deductive-system 𝓤 𝓥 ,
 is-pos-depolarized 𝓓

depolarized-deductive-system-to-precategory
 : depolarized-deductive-system 𝓤 𝓥
 → precategory 𝓤 𝓥
depolarized-deductive-system-to-precategory (𝓓 , H) =
 let open depolarization-and-precategories in
 precategory-of-depolarized-deductive-system 𝓓 H

precategory-to-depolarized-deductive-system
 : precategory 𝓤 𝓥
 → depolarized-deductive-system 𝓤 𝓥
precategory-to-depolarized-deductive-system 𝓒 =
 𝓓 , precategory-gives-pos-depolarized 𝓓 (pr₂ 𝓒)
 where
  open precategory 𝓒
  open depolarization-and-precategories
  𝓓 : deductive-system _ _
  𝓓 = pr₁ 𝓒 , hom-is-set , idn-L , idn-R

module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥)) (fe1 : funext 𝓥 (𝓤 ⊔ 𝓥)) where
 private
  fe2 : funext 𝓥 𝓥
  fe2 = lower-funext 𝓥 𝓤 fe1

 depolarized-deductive-system-to-precategory-is-equiv
  : is-equiv (depolarized-deductive-system-to-precategory {𝓤} {𝓥})
 depolarized-deductive-system-to-precategory-is-equiv = H
  where
   H : is-equiv (depolarized-deductive-system-to-precategory {𝓤} {𝓥})
   pr₁ H =
    precategory-to-depolarized-deductive-system ,
    λ 𝓒 → to-Σ-＝ (refl , precategory-axioms-is-prop (pr₁ 𝓒) fe0 fe2 _ _)
   pr₂ H =
    precategory-to-depolarized-deductive-system ,
    λ (𝓓 , _) → to-Σ-＝ (refl , being-pos-depolarized-is-prop 𝓓 fe0 fe1 _ _)

\end{code}
