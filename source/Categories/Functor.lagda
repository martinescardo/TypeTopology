Jon Sterling, started 16th Dec 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Categories.Functor where

open import MLTT.Spartan
open import UF.FunExt
open import UF.Base
open import UF.Equiv
open import UF.Lower-FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Equiv-FunExt

open import Categories.Category

module functor-of-precategories (𝓒 𝓓 : precategory 𝓤 𝓥) where
 private
  module 𝓒 = precategory 𝓒
  module 𝓓 = precategory 𝓓

 functor-structure : 𝓤 ⊔ 𝓥 ̇
 functor-structure =
  Σ ob ꞉ (𝓒.ob → 𝓓.ob) ,
  ({A B : 𝓒.ob} (f : 𝓒.hom A B) → 𝓓.hom (ob A) (ob B))

 module functor-structure (F : functor-structure) where
  ob : 𝓒.ob → 𝓓.ob
  ob = pr₁ F

  hom : {A B : 𝓒.ob} (f : 𝓒.hom A B) → 𝓓.hom (ob A) (ob B)
  hom = pr₂ F

 module _ (F : functor-structure) where
  open functor-structure F

  statement-preserves-idn : 𝓤 ⊔ 𝓥 ̇
  statement-preserves-idn =
   (A : 𝓒.ob)
   → hom (𝓒.idn A) ＝ 𝓓.idn (ob A)

  statement-preserves-seq : 𝓤 ⊔ 𝓥 ̇
  statement-preserves-seq =
   (A B C : 𝓒.ob)
   → (f : 𝓒.hom A B)
   → (g : 𝓒.hom B C)
   → hom (𝓒.seq f g) ＝ 𝓓.seq (hom f) (hom g)

  functor-axioms : 𝓤 ⊔ 𝓥 ̇
  functor-axioms =
   statement-preserves-idn
   × statement-preserves-seq


  module _ (fe : funext 𝓤 𝓥) where
   preserving-idn-is-prop : is-prop statement-preserves-idn
   preserving-idn-is-prop =
    Π-is-prop fe λ _ →
    𝓓.hom-is-set _ _

  module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥)) (fe1 : funext 𝓥 𝓥) where
   private
    fe2 : funext 𝓤 𝓥
    fe2 = lower-funext 𝓤 𝓤 fe0

   preserving-seq-is-prop : is-prop statement-preserves-seq
   preserving-seq-is-prop =
    Π-is-prop fe0 λ _ →
    Π-is-prop fe0 λ _ →
    Π-is-prop fe2 λ _ →
    Π-is-prop fe1 λ _ →
    Π-is-prop fe1 λ _ →
    𝓓.hom-is-set _ _

   functor-axioms-is-prop : is-prop functor-axioms
   functor-axioms-is-prop =
    ×-is-prop
     (preserving-idn-is-prop fe2)
     preserving-seq-is-prop


module functor-of-categories (𝓒 𝓓 : category 𝓤 𝓥) where
  open
   functor-of-precategories
    (category-to-precategory 𝓒)
    (category-to-precategory 𝓓)
   public
