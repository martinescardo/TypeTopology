Jon Sterling, started 16th Dec 2022

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module deprecated.Categories.Functor (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Equiv
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import deprecated.Categories.Category fe

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

  preserving-idn-is-prop : is-prop statement-preserves-idn
  preserving-idn-is-prop =
   Π-is-prop fe λ _ →
   𝓓.hom-is-set _ _

  preserving-seq-is-prop : is-prop statement-preserves-seq
  preserving-seq-is-prop =
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   𝓓.hom-is-set _ _

  functor-axioms-is-prop : is-prop functor-axioms
  functor-axioms-is-prop =
   ×-is-prop
    preserving-idn-is-prop
    preserving-seq-is-prop

 record functor : 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇ where
  constructor make
  field
   str : functor-structure
   ax : functor-axioms str

  open functor-structure str public
  open functor-axioms str ax public

 module functor-as-sum where
  to-sum : functor → Σ functor-axioms
  to-sum F = let open functor F in str , ax

  from-sum : Σ functor-axioms → functor
  from-sum F = make (pr₁ F) (pr₂ F)

  to-sum-is-equiv : is-equiv to-sum
  pr₁ (pr₁ to-sum-is-equiv) = from-sum
  pr₂ (pr₁ to-sum-is-equiv) _ = refl
  pr₁ (pr₂ to-sum-is-equiv) = from-sum
  pr₂ (pr₂ to-sum-is-equiv) _ = refl

  equiv : functor ≃ Σ functor-axioms
  equiv = to-sum , to-sum-is-equiv


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
 fun = make str ax

module composite-functor
 {𝓒 : precategory 𝓣 𝓤} {𝓓 : precategory 𝓣' 𝓤'} {𝓔 : precategory 𝓥 𝓦}
 (open functor-of-precategories)
 (F : functor 𝓒 𝓓)
 (G : functor 𝓓 𝓔)
 where

 private
  module 𝓒 = precategory 𝓒
  module 𝓓 = precategory 𝓓
  module 𝓔 = precategory 𝓔
  module F = functor F
  module G = functor G

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
 fun = make str ax
