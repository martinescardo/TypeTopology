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
  open polarities 𝓓

  -- We could consider three forms of depolarization:
  -- 1. All objects have positive polarity
  -- 2. All objects have negative polarity
  -- 3. Either (1) or (2).

  is-positively-depolarized : 𝓤 ⊔ 𝓥 ̇
  is-positively-depolarized = (A : ob) → is-positive A

  is-negatively-depolarized : 𝓤 ⊔ 𝓥 ̇
  is-negatively-depolarized = (A : ob) → is-negative A

  depolarization : 𝓤 ⊔ 𝓥 ̇
  depolarization = is-positively-depolarized + is-negatively-depolarized

  is-depolarized : 𝓤 ⊔ 𝓥 ̇
  is-depolarized = ∥ depolarization ∥

  -- It turns out that all three forms of depolarization are equivalent.
  -- But we will use `is-depolarized` because it is the most symmetrical.

  is-positively-depolarized-gives-is-negatively-depolarized
   : is-positively-depolarized
   → is-negatively-depolarized
  is-positively-depolarized-gives-is-negatively-depolarized pos A B f C D g h =
   pos C D h B A g f

  is-negatively-depolarized-gives-is-positively-depolarized
   : is-negatively-depolarized
   → is-positively-depolarized
  is-negatively-depolarized-gives-is-positively-depolarized neg A B f U V g h =
   neg V U h A B g f


  module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥)) (fe1 : funext 𝓥 (𝓤 ⊔ 𝓥)) where
   is-depolarized-gives-is-positively-depolarized
    : is-depolarized
    → is-positively-depolarized
   is-depolarized-gives-is-positively-depolarized =
    ∥∥-rec (Π-is-prop fe0 λ _ → is-positive-is-prop fe0 fe1) case
    where
     case : depolarization → is-positively-depolarized
     case (inl pos) = pos
     case (inr neg) = is-negatively-depolarized-gives-is-positively-depolarized neg

   is-depolarized-gives-is-negatively-depolarized
    : is-depolarized
    → is-negatively-depolarized
   is-depolarized-gives-is-negatively-depolarized =
    is-positively-depolarized-gives-is-negatively-depolarized
    ∘ is-depolarized-gives-is-positively-depolarized

  module _ (depol : is-depolarized) where
   depolarization-gives-assoc : category-axiom-statements.statement-assoc (pr₁ 𝓓)
   depolarization-gives-assoc A B C D f g h =
    ∥∥-rec (⊢-is-set A D) case depol
    where
     case : depolarization → cut f (cut g h) ＝ cut (cut f g) h
     case (inl pos) = pos C D h A B g f ⁻¹
     case (inr neg) = neg B A f C D g h ⁻¹


   depolarization-gives-precategory : precategory-axioms (pr₁ 𝓓)
   depolarization-gives-precategory =
    ⊢-is-set ,
    idn-L ,
    idn-R ,
    depolarization-gives-assoc

  module _ (ax : precategory-axioms (pr₁ 𝓓)) where
   module ax = precategory-axioms (pr₁ 𝓓) ax

   precategory-gives-positively-depolarized : (A : ob) → is-positive A
   precategory-gives-positively-depolarized A B f U V g h =
    ax.assoc U V A B h g f ⁻¹

   precategory-gives-negatively-depolarized : (A : ob) → is-negative A
   precategory-gives-negatively-depolarized A B f U V g h =
    ax.assoc B A U V f g h ⁻¹




\end{code}
