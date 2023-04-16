Jon Sterling, started 24th Feb 2023

Several *categories* can be obtained from a given preduploid:

1. The category of negative objects and all maps.
2. The category of positive objects and all maps.
3. The category of negative objects and linear maps.
4. The category of positive objects and linear maps.

We define these below, and they will play a role in the structure theorem that
identifies duploids with adjunctions; it is also possible to consider the full
subcategories of a preduploid spanned by linear or thunkable maps. We have not
implemented these yet.


\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import Duploids.Preduploid

module Duploids.Categories
 (fe : Fun-Ext)
 (pt : propositional-truncations-exist)
 (𝓓 : preduploid fe pt 𝓤 𝓥)
 where

open import UF.Base
open import UF.Retracts
open import UF.Subsingletons
open import Duploids.Duploid fe pt

open import Categories.Category fe
open preduploid-extras fe pt 𝓓
private
 module 𝓓 = preduploid 𝓓

open duploid-axioms 𝓓.underlying-deductive-system

module NegativesAndAllMaps where
 ob : 𝓤 ⊔ 𝓥 ̇
 ob = Σ A ꞉ 𝓓.ob , 𝓓.is-negative A

 hom : ob → ob → 𝓥 ̇
 hom A B = pr₁ A 𝓓.⊢ pr₁ B

 idn : (A : ob) → hom A A
 idn A = 𝓓.idn (pr₁ A)

 seq' : (A B C : ob) → hom A B → hom B C → hom A C
 seq' A B C f g = 𝓓.cut f g

 cat-data : category-structure (𝓤 ⊔ 𝓥) 𝓥
 cat-data = ob , hom , idn , seq'

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
  precat = make ob hom idn seq' (hom-is-set , idn-L , idn-R , assoc)

module PositivesAndAllMaps where
 ob : 𝓤 ⊔ 𝓥 ̇
 ob = Σ A ꞉ 𝓓.ob , 𝓓.is-positive A

 hom : ob → ob → 𝓥 ̇
 hom A B = pr₁ A 𝓓.⊢ pr₁ B

 idn : (A : ob) → hom A A
 idn A = 𝓓.idn (pr₁ A)

 seq' : (A B C : ob) → hom A B → hom B C → hom A C
 seq' _ _ _ f g = 𝓓.cut f g

 cat-data : category-structure (𝓤 ⊔ 𝓥) 𝓥
 cat-data = ob , hom , idn , seq'

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
  precat = make ob hom idn seq' (hom-is-set , idn-L , idn-R , assoc)


module NegativesAndLinearMaps where
 ob : 𝓤 ⊔ 𝓥 ̇
 ob = Σ A ꞉ 𝓓.ob , 𝓓.is-negative A

 hom : ob → ob → 𝓤 ⊔ 𝓥 ̇
 hom A B = Σ f ꞉ (pr₁ A 𝓓.⊢ pr₁ B) , 𝓓.is-linear f

 idn : (A : ob) → hom A A
 pr₁ (idn A) = 𝓓.idn (pr₁ A)
 pr₂ (idn A) = idn-linear (pr₁ A)

 seq' : (A B C : ob) → hom A B → hom B C → hom A C
 pr₁ (seq' _ _ _ f g) = 𝓓.cut (pr₁ f) (pr₁ g)
 pr₂ (seq' _ _ _ f g) = cut-linear (pr₁ f) (pr₁ g) (pr₂ f) (pr₂ g)

 cat-data : category-structure (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
 cat-data = ob , hom , idn , seq'

 open category-axiom-statements

 module _ (A B : ob) (f g : hom A B) where
  to-hom-＝ : pr₁ f ＝ pr₁ g → f ＝ g
  to-hom-＝ h = to-Σ-＝ (h , 𝓓.being-linear-is-prop _ _)

 hom-is-set : statement-hom-is-set cat-data
 hom-is-set A B =
  Σ-is-set (𝓓.⊢-is-set (pr₁ A) (pr₁ B)) λ _ →
  props-are-sets 𝓓.being-linear-is-prop

 idn-L : statement-idn-L cat-data
 idn-L A B f = to-hom-＝ A B _ _ (𝓓.idn-L (pr₁ A) (pr₁ B) (pr₁ f))

 idn-R : statement-idn-R cat-data
 idn-R A B f = to-hom-＝ A B _ _ (𝓓.idn-R (pr₁ A) (pr₁ B) (pr₁ f))

 assoc : statement-assoc cat-data
 assoc A B C D f g h =
  to-hom-＝ A D _ _
   (pr₂ B (pr₁ A) (pr₁ f) (pr₁ C) (pr₁ D) (pr₁ g) (pr₁ h) ⁻¹)

 precat : precategory (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
 precat = make ob hom idn seq' (hom-is-set , idn-L , idn-R , assoc)

 module _ (nuni : is-negatively-univalent) where
  open hom-properties precat

  precat-is-univalent : is-univalent-precategory precat
  precat-is-univalent A (B0 , f0 , g0 , fg0 , gf0) (B1 , f1 , g1 , fg1 , gf1) =
   B0 , f0 , g0 , fg0 , gf0
    ＝⟨ ap (λ - → B0 , f0 , g0 , -) (being-inverse-is-prop {B0} {A} _ _ _ _) ⟩
   B0 , f0 , g0 , _ , _ ＝⟨ lem ⟩
   B1 , f1 , g1 , _ , _
    ＝⟨ ap (λ - → B1 , f1 , g1 , -) (being-inverse-is-prop {B1} {A} _ _ _ _) ⟩
   B1 , f1 , g1 , fg1 , gf1 ∎
   where
    nliso0 : negative-linear-isomorph (pr₁ A)
    nliso0 = pr₁ B0 , pr₁ f0 , pr₁ g0 , pr₂ B0 , pr₂ f0 , pr₂ g0 , ap pr₁ fg0 , ap pr₁ gf0

    nliso1 : negative-linear-isomorph (pr₁ A)
    nliso1 = pr₁ B1 , pr₁ f1 , pr₁ g1 , pr₂ B1 , pr₂ f1 , pr₂ g1 , ap pr₁ fg1 , ap pr₁ gf1

    nliso01 : nliso0 ＝ nliso1
    nliso01 = nuni (pr₁ A) (pr₂ A) nliso0 nliso1

    lem : _＝_ {_} {isomorph precat A} (B0 , f0 , g0 , _) (B1 , f1 , g1 , _)
    lem =
     ap (λ (B , f , g , B-neg , f-lin , g-lin , fg , gf) →
      (B , B-neg) , (f , f-lin) , (g , g-lin) ,
      to-Σ-＝ (fg , 𝓓.being-linear-is-prop _ _) ,
      to-Σ-＝ (gf , 𝓓.being-linear-is-prop _ _)
     ) nliso01

  cat : category (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
  cat = precat , precat-is-univalent


module PositivesAndThunkableMaps where
 ob : 𝓤 ⊔ 𝓥 ̇
 ob = Σ A ꞉ 𝓓.ob , 𝓓.is-positive A

 hom : ob → ob → 𝓤 ⊔ 𝓥 ̇
 hom A B = Σ f ꞉ (pr₁ A 𝓓.⊢ pr₁ B) , 𝓓.is-thunkable f

 idn : (A : ob) → hom A A
 pr₁ (idn A) = 𝓓.idn (pr₁ A)
 pr₂ (idn A) = idn-thunkable (pr₁ A)

 seq' : (A B C : ob) → hom A B → hom B C → hom A C
 pr₁ (seq' _ _ _ f g) = 𝓓.cut (pr₁ f) (pr₁ g)
 pr₂ (seq' _ _ _ f g) = cut-thunkable (pr₁ f) (pr₁ g) (pr₂ f) (pr₂ g)

 cat-data : category-structure (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
 cat-data = ob , hom , idn , seq'

 open category-axiom-statements

 module _ (A B : ob) (f g : hom A B) where
  to-hom-＝ : pr₁ f ＝ pr₁ g → f ＝ g
  to-hom-＝ h = to-Σ-＝ (h , 𝓓.being-thunkable-is-prop _ _)

 hom-is-set : statement-hom-is-set cat-data
 hom-is-set A B =
  Σ-is-set (𝓓.⊢-is-set (pr₁ A) (pr₁ B)) λ _ →
  props-are-sets 𝓓.being-thunkable-is-prop

 idn-L : statement-idn-L cat-data
 idn-L A B f = to-hom-＝ A B _ _ (𝓓.idn-L (pr₁ A) (pr₁ B) (pr₁ f))

 idn-R : statement-idn-R cat-data
 idn-R A B f = to-hom-＝ A B _ _ (𝓓.idn-R (pr₁ A) (pr₁ B) (pr₁ f))

 assoc : statement-assoc cat-data
 assoc A B C D f g h =
  to-hom-＝ A D _ _
   (pr₂ C (pr₁ D) (pr₁ h) (pr₁ A) (pr₁ B) (pr₁ g) (pr₁ f) ⁻¹)

 precat : precategory (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
 precat = make ob hom idn seq' (hom-is-set , idn-L , idn-R , assoc)


 module _ (puni : is-positively-univalent) where
  open hom-properties precat

  precat-is-univalent : is-univalent-precategory precat
  precat-is-univalent A (B0 , f0 , g0 , fg0 , gf0) (B1 , f1 , g1 , fg1 , gf1) =
   B0 , f0 , g0 , fg0 , gf0
    ＝⟨ ap (λ - → B0 , f0 , g0 , -) (being-inverse-is-prop {B0} {A} _ _ _ _) ⟩
   B0 , f0 , g0 , _ , _ ＝⟨ lem ⟩
   B1 , f1 , g1 , _ , _
    ＝⟨ ap (λ - → B1 , f1 , g1 , -) (being-inverse-is-prop {B1} {A} _ _ _ _) ⟩
   B1 , f1 , g1 , fg1 , gf1 ∎
   where
    pthiso0 : positive-thunkable-isomorph (pr₁ A)
    pthiso0 = pr₁ B0 , pr₁ f0 , pr₁ g0 , pr₂ B0 , pr₂ f0 , pr₂ g0 , ap pr₁ fg0 , ap pr₁ gf0

    pthiso1 : positive-thunkable-isomorph (pr₁ A)
    pthiso1 = pr₁ B1 , pr₁ f1 , pr₁ g1 , pr₂ B1 , pr₂ f1 , pr₂ g1 , ap pr₁ fg1 , ap pr₁ gf1

    pthiso01 : pthiso0 ＝ pthiso1
    pthiso01 = puni (pr₁ A) (pr₂ A) pthiso0 pthiso1

    lem : _＝_ {_} {isomorph precat A} (B0 , f0 , g0 , _) (B1 , f1 , g1 , _)
    lem =
     ap (λ (B , f , g , B-pos , f-th , g-th , fg , gf) →
      (B , B-pos) , (f , f-th) , (g , g-th) ,
      to-Σ-＝ (fg , 𝓓.being-thunkable-is-prop _ _) ,
      to-Σ-＝ (gf , 𝓓.being-thunkable-is-prop _ _)
     ) pthiso01

  cat : category (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
  cat = precat , precat-is-univalent

\end{code}


\begin{code}
𝓟 = PositivesAndAllMaps.precat
𝓝 = NegativesAndAllMaps.precat
𝓒 = PositivesAndThunkableMaps.precat
𝓢 = NegativesAndLinearMaps.precat

module 𝓟 = precategory 𝓟
module 𝓝 = precategory 𝓝
module 𝓒 = precategory 𝓒
module 𝓢 = precategory 𝓢
\end{code}
