Jon Sterling, started 16th Dec 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF.PropTrunc

module Machines.Preduploid (pt : propositional-truncations-exist) where

open PropositionalTruncation pt

open import MLTT.Spartan
open import UF.FunExt
open import UF.Base
open import UF.Equiv
open import UF.Retracts
open import UF.hlevels
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import Categories.Category
open import Machines.DeductiveSystem

module _ (𝓓 : deductive-system 𝓤 𝓥) where
 open deductive-system 𝓓
 open ⊢-properties 𝓓
 open polarities 𝓓

 is-polarized : (A : ob) → 𝓤 ⊔ 𝓥 ̇
 is-polarized A = ∥ is-positive A + is-negative A ∥

 being-polarized-is-prop : {A : ob} → is-prop (is-polarized A)
 being-polarized-is-prop = ∥∥-is-prop

 preduploid-axioms : 𝓤 ⊔ 𝓥 ̇
 preduploid-axioms = (A : ob) → is-polarized A

 module _ (fe : funext 𝓤 (𝓤 ⊔ 𝓥)) where
  preduploid-axioms-is-prop : is-prop preduploid-axioms
  preduploid-axioms-is-prop =
   Π-is-prop fe λ _ →
   being-polarized-is-prop

preduploid : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
preduploid 𝓤 𝓥 =  Σ 𝓓 ꞉ deductive-system 𝓤 𝓥 , preduploid-axioms 𝓓

module preduploid (𝓓 : preduploid 𝓤 𝓥) where

 underlying-deductive-system : deductive-system 𝓤 𝓥
 underlying-deductive-system = pr₁ 𝓓

 open deductive-system underlying-deductive-system public

 ob-is-polarized : (A : ob) → is-polarized underlying-deductive-system A
 ob-is-polarized = pr₂ 𝓓

 -- I don't know the correct univalence/saturation conditions yet for a preduploid

 module preduploid-univalence where
  open polarities underlying-deductive-system
  open ⊢-properties underlying-deductive-system

  module _ (A B : ob) where
   module _ (f : A ⊢ B) where
    is-thunkable-iso : 𝓤 ⊔ 𝓥 ̇
    is-thunkable-iso = is-thunkable f × (Σ g ꞉ (B ⊢ A) , is-inverse f g)

    is-linear-iso : 𝓤 ⊔ 𝓥 ̇
    is-linear-iso = is-linear f × (Σ g ꞉ (B ⊢ A) , is-inverse f g)

   thunkable-iso : 𝓤 ⊔ 𝓥 ̇
   thunkable-iso = Σ f ꞉ A ⊢ B , is-thunkable-iso f

   linear-iso : 𝓤 ⊔ 𝓥 ̇
   linear-iso = Σ f ꞉ A ⊢ B , is-linear-iso f

  ＝-to-thunkable-iso : (A B : ob) → A ＝ B → thunkable-iso A B
  ＝-to-thunkable-iso A .A refl =
   idn A , idn-thunkable A , idn A , idn-L _ _ _ , idn-L _ _ _

  ＝-to-linear-iso : (A B : ob) → A ＝ B → linear-iso A B
  ＝-to-linear-iso A B refl =
   idn A , idn-linear A , idn A , idn-L _ _ _ , idn-L _ _ _

  is-positively-univalent : 𝓤 ⊔ 𝓥 ̇
  is-positively-univalent =
   (A B : ob)
   → is-positive A
   → is-positive B
   → is-equiv (＝-to-thunkable-iso A B)

  is-negatively-univalent : 𝓤 ⊔ 𝓥 ̇
  is-negatively-univalent =
   (A B : ob)
   → is-negative A
   → is-negative B
   → is-equiv (＝-to-linear-iso A B)

  is-univalent : 𝓤 ⊔ 𝓥 ̇
  is-univalent = is-positively-univalent × is-negatively-univalent


module NegativesAndAllMaps (𝓓 : preduploid 𝓤 𝓥) where
 module 𝓓 = preduploid 𝓓
 open polarities (pr₁ 𝓓)

 ob : 𝓤 ⊔ 𝓥 ̇
 ob = Σ A ꞉ 𝓓.ob , is-negative A

 hom : ob → ob → 𝓥 ̇
 hom A B = pr₁ A 𝓓.⊢ pr₁ B

 idn : (A : ob) → hom A A
 idn A = 𝓓.idn (pr₁ A)

 seq : (A B C : ob) → hom A B → hom B C → hom A C
 seq _ _ _ f g = 𝓓.cut f g

 cat-data : category-structure (𝓤 ⊔ 𝓥) 𝓥
 cat-data = ob , hom , idn , seq

 module _ (open category-axiom-statements) where
  hom-is-set : statement-hom-is-set cat-data
  hom-is-set A B = 𝓓.⊢-is-set (pr₁ A) (pr₁ B)

  idn-L : statement-idn-L cat-data
  idn-L A B = 𝓓.idn-L (pr₁ A) (pr₁ B)

  idn-R : statement-idn-R cat-data
  idn-R A B = 𝓓.idn-R (pr₁ A) (pr₁ B)

  assoc : statement-assoc cat-data
  assoc A B C D f g h = pr₂ B (pr₁ A) f (pr₁ C) (pr₁ D) g h ⁻¹

  precat : precategory (𝓤 ⊔ 𝓥) 𝓥
  precat = cat-data , hom-is-set , idn-L , idn-R , assoc

module PositivesAndAllMaps (𝓓 : preduploid 𝓤 𝓥) where
 module 𝓓 = preduploid 𝓓
 open polarities (pr₁ 𝓓)

 ob : 𝓤 ⊔ 𝓥 ̇
 ob = Σ A ꞉ 𝓓.ob , is-positive A

 hom : ob → ob → 𝓥 ̇
 hom A B = pr₁ A 𝓓.⊢ pr₁ B

 idn : (A : ob) → hom A A
 idn A = 𝓓.idn (pr₁ A)

 seq : (A B C : ob) → hom A B → hom B C → hom A C
 seq _ _ _ f g = 𝓓.cut f g

 cat-data : category-structure (𝓤 ⊔ 𝓥) 𝓥
 cat-data = ob , hom , idn , seq

 module _ (open category-axiom-statements) where
  hom-is-set : statement-hom-is-set cat-data
  hom-is-set A B = 𝓓.⊢-is-set (pr₁ A) (pr₁ B)

  idn-L : statement-idn-L cat-data
  idn-L A B = 𝓓.idn-L (pr₁ A) (pr₁ B)

  idn-R : statement-idn-R cat-data
  idn-R A B = 𝓓.idn-R (pr₁ A) (pr₁ B)

  assoc : statement-assoc cat-data
  assoc A B C D f g h = pr₂ C (pr₁ D) h (pr₁ A) (pr₁ B) g f ⁻¹

  precat : precategory (𝓤 ⊔ 𝓥) 𝓥
  precat = cat-data , hom-is-set , idn-L , idn-R , assoc


module NegativesAndLinearMaps (𝓓 : preduploid 𝓤 𝓥) where
 module 𝓓 = preduploid 𝓓
 open polarities (pr₁ 𝓓)
 open ⊢-properties (pr₁ 𝓓)

 ob : 𝓤 ⊔ 𝓥 ̇
 ob = Σ A ꞉ 𝓓.ob , is-negative A

 hom : ob → ob → 𝓤 ⊔ 𝓥 ̇
 hom A B = Σ f ꞉ (pr₁ A 𝓓.⊢ pr₁ B) , is-linear f

 idn : (A : ob) → hom A A
 pr₁ (idn A) = 𝓓.idn (pr₁ A)
 pr₂ (idn A) = idn-linear (pr₁ A)

 seq : (A B C : ob) → hom A B → hom B C → hom A C
 pr₁ (seq _ _ _ f g) = 𝓓.cut (pr₁ f) (pr₁ g)
 pr₂ (seq _ _ _ f g) = cut-linear (pr₁ f) (pr₁ g) (pr₂ f) (pr₂ g)

 cat-data : category-structure (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
 cat-data = ob , hom , idn , seq

 module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥)) (fe1 : funext 𝓥 𝓥) where
  open category-axiom-statements

  module _ (A B : ob) (f g : hom A B) where
   to-hom-＝ : pr₁ f ＝ pr₁ g → f ＝ g
   to-hom-＝ h = to-Σ-＝ (h , being-linear-is-prop fe0 fe1 _ _)

  hom-is-set : statement-hom-is-set cat-data
  hom-is-set A B =
   Σ-is-set (𝓓.⊢-is-set (pr₁ A) (pr₁ B)) λ _ →
   props-are-sets (being-linear-is-prop fe0 fe1)

  idn-L : statement-idn-L cat-data
  idn-L A B f = to-hom-＝ A B _ _ (𝓓.idn-L (pr₁ A) (pr₁ B) (pr₁ f))

  idn-R : statement-idn-R cat-data
  idn-R A B f = to-hom-＝ A B _ _ (𝓓.idn-R (pr₁ A) (pr₁ B) (pr₁ f))

  assoc : statement-assoc cat-data
  assoc A B C D f g h =
   to-hom-＝ A D _ _
    (pr₂ B (pr₁ A) (pr₁ f) (pr₁ C) (pr₁ D) (pr₁ g) (pr₁ h) ⁻¹)

  precat : precategory (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
  precat = cat-data , hom-is-set , idn-L , idn-R , assoc


module PositivesAndThunkableMaps (𝓓 : preduploid 𝓤 𝓥) where
 module 𝓓 = preduploid 𝓓
 open polarities (pr₁ 𝓓)
 open ⊢-properties (pr₁ 𝓓)

 ob : 𝓤 ⊔ 𝓥 ̇
 ob = Σ A ꞉ 𝓓.ob , is-positive A

 hom : ob → ob → 𝓤 ⊔ 𝓥 ̇
 hom A B = Σ f ꞉ (pr₁ A 𝓓.⊢ pr₁ B) , is-thunkable f

 idn : (A : ob) → hom A A
 pr₁ (idn A) = 𝓓.idn (pr₁ A)
 pr₂ (idn A) = idn-thunkable (pr₁ A)

 seq : (A B C : ob) → hom A B → hom B C → hom A C
 pr₁ (seq _ _ _ f g) = 𝓓.cut (pr₁ f) (pr₁ g)
 pr₂ (seq _ _ _ f g) = cut-thunkable (pr₁ f) (pr₁ g) (pr₂ f) (pr₂ g)

 cat-data : category-structure (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
 cat-data = ob , hom , idn , seq

 module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥)) (fe1 : funext 𝓥 𝓥) where
  open category-axiom-statements

  module _ (A B : ob) (f g : hom A B) where
   to-hom-＝ : pr₁ f ＝ pr₁ g → f ＝ g
   to-hom-＝ h = to-Σ-＝ (h , being-thunkable-is-prop fe0 fe1 _ _)

  hom-is-set : statement-hom-is-set cat-data
  hom-is-set A B =
   Σ-is-set (𝓓.⊢-is-set (pr₁ A) (pr₁ B)) λ _ →
   props-are-sets (being-thunkable-is-prop fe0 fe1)

  idn-L : statement-idn-L cat-data
  idn-L A B f = to-hom-＝ A B _ _ (𝓓.idn-L (pr₁ A) (pr₁ B) (pr₁ f))

  idn-R : statement-idn-R cat-data
  idn-R A B f = to-hom-＝ A B _ _ (𝓓.idn-R (pr₁ A) (pr₁ B) (pr₁ f))

  assoc : statement-assoc cat-data
  assoc A B C D f g h =
   to-hom-＝ A D _ _
    (pr₂ C (pr₁ D) (pr₁ h) (pr₁ A) (pr₁ B) (pr₁ g) (pr₁ f) ⁻¹)

  precat : precategory (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
  precat = cat-data , hom-is-set , idn-L , idn-R , assoc




\end{code}
