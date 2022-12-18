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

module functor-of-precategories (𝓒 : precategory 𝓤 𝓥) (𝓓 : precategory 𝓤' 𝓥') where
 private
  module 𝓒 = precategory 𝓒
  module 𝓓 = precategory 𝓓

 functor-structure : 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇
 functor-structure =
  Σ ob ꞉ (𝓒.ob → 𝓓.ob) ,
  ((A B : 𝓒.ob) (f : 𝓒.hom A B) → 𝓓.hom (ob A) (ob B))

 module functor-structure (F : functor-structure) where
  ob : 𝓒.ob → 𝓓.ob
  ob = pr₁ F

  hom : {A B : 𝓒.ob} (f : 𝓒.hom A B) → 𝓓.hom (ob A) (ob B)
  hom = pr₂ F _ _

 module _ (F : functor-structure) where
  open functor-structure F

  statement-preserves-idn : 𝓤 ⊔ 𝓥' ̇
  statement-preserves-idn =
   (A : 𝓒.ob)
   → hom (𝓒.idn A) ＝ 𝓓.idn (ob A)

  statement-preserves-seq : 𝓤 ⊔ 𝓥 ⊔ 𝓥' ̇
  statement-preserves-seq =
   (A B C : 𝓒.ob)
   → (f : 𝓒.hom A B)
   → (g : 𝓒.hom B C)
   → hom (𝓒.seq f g) ＝ 𝓓.seq (hom f) (hom g)

  functor-axioms : 𝓤 ⊔ 𝓥 ⊔ 𝓥' ̇
  functor-axioms =
   statement-preserves-idn
   × statement-preserves-seq

  module functor-axioms (ax : functor-axioms) where
   preserves-idn : statement-preserves-idn
   preserves-idn = pr₁ ax

   preserves-seq : statement-preserves-seq
   preserves-seq = pr₂ ax

  module _ (fe : funext 𝓤 𝓥') where
   preserving-idn-is-prop : is-prop statement-preserves-idn
   preserving-idn-is-prop =
    Π-is-prop fe λ _ →
    𝓓.hom-is-set _ _

  module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥 ⊔ 𝓥')) (fe1 : funext 𝓥 (𝓥 ⊔ 𝓥')) where
   private
    fe2 : funext 𝓤 𝓥
    fe2 = lower-funext 𝓤 (𝓤 ⊔ 𝓥') fe0

    fe3 : funext 𝓤 (𝓥 ⊔ 𝓥')
    fe3 = lower-funext 𝓤 𝓤 fe0

    fe4 : funext 𝓥 𝓥'
    fe4 = lower-funext 𝓥 𝓥 fe1

    fe5 : funext 𝓤 𝓥'
    fe5 = lower-funext 𝓤 (𝓤 ⊔ 𝓥) fe0

   preserving-seq-is-prop : is-prop statement-preserves-seq
   preserving-seq-is-prop =
    Π-is-prop fe0 λ _ →
    Π-is-prop fe0 λ _ →
    Π-is-prop fe3 λ _ →
    Π-is-prop fe1 λ _ →
    Π-is-prop fe4 λ _ →
    𝓓.hom-is-set _ _

   functor-axioms-is-prop : is-prop functor-axioms
   functor-axioms-is-prop =
    ×-is-prop
     (preserving-idn-is-prop fe5)
     preserving-seq-is-prop

 functor : 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇
 functor = Σ F ꞉ functor-structure , functor-axioms F

 module functor (F : functor) where
  open functor-structure (pr₁ F) public
  open functor-axioms (pr₁ F) (pr₂ F) public

module functor-of-categories (𝓒 𝓓 : category 𝓤 𝓥) where
  open
   functor-of-precategories
    (category-to-precategory 𝓒)
    (category-to-precategory 𝓓)
   public


module identity-functor (𝓒 : precategory 𝓤 𝓥) where
 open functor-of-precategories

 str : functor-structure 𝓒 𝓒
 str = id , λ _ _ → id

 ax : functor-axioms 𝓒 𝓒 str
 ax = (λ A → refl) , (λ A B C f g → refl)

 fun : functor 𝓒 𝓒
 fun = str , ax

module composite-functor
 (𝓒 : precategory 𝓣 𝓤) (𝓓 : precategory 𝓣' 𝓤') (𝓔 : precategory 𝓥 𝓦)
 (open functor-of-precategories)
 (F : functor 𝓒 𝓓)
 (G : functor 𝓓 𝓔)
 where

 private
  module 𝓒 = precategory 𝓒
  module 𝓓 = precategory 𝓓
  module 𝓔 = precategory 𝓔
  module F = functor 𝓒 𝓓 F
  module G = functor 𝓓 𝓔 G

 ob : 𝓒.ob → 𝓔.ob
 ob A = G.ob (F.ob A)

 hom : (A B : 𝓒.ob) (f : 𝓒.hom A B) → 𝓔.hom (ob A) (ob B)
 hom A B f = G.hom (F.hom f)

 str : functor-structure 𝓒 𝓔
 str = ob , hom

 preserves-idn : (A : 𝓒.ob) → hom A A (𝓒.idn A) ＝ 𝓔.idn (ob A)
 preserves-idn A =
  G.hom (F.hom (𝓒.idn A)) ＝⟨ ap G.hom (F.preserves-idn A) ⟩
  G.hom (𝓓.idn (F.ob A)) ＝⟨ G.preserves-idn (F.ob A) ⟩
  𝓔.idn (ob A) ∎

 preserves-seq
  : (A B C : 𝓒.ob) (f : 𝓒.hom A B) (g : 𝓒.hom B C)
  → hom A C (𝓒.seq f g) ＝ 𝓔.seq (hom A B f) (hom B C g)
 preserves-seq A B C f g =
  G.hom (F.hom (𝓒.seq f g))
   ＝⟨ ap G.hom (F.preserves-seq A B C f g) ⟩
  G.hom (𝓓.seq (F.hom f) (F.hom g))
   ＝⟨ G.preserves-seq (F.ob A) (F.ob B) (F.ob C) (F.hom f) (F.hom g) ⟩
  𝓔.seq (G.hom (F.hom f)) (G.hom (F.hom g)) ∎

 ax : functor-axioms 𝓒 𝓔 str
 ax = preserves-idn , preserves-seq

 fun : functor 𝓒 𝓔
 fun = str , ax
