Jon Sterling, started 16th Dec 2022

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module deprecated.Categories.Category (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Equiv-FunExt
open import UF.Sets
open import UF.Sets-Properties

\end{code}

We prefer composition in diagrammatic order.

\begin{code}

category-structure : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
category-structure 𝓤 𝓥 =
 Σ ob ꞉ (𝓤 ̇ ),
 Σ hom ꞉ (ob → ob → 𝓥 ̇ ),
 Σ idn ꞉ ((A : ob) → hom A A) ,
 ((A B C : ob) (f : hom A B) (g : hom B C) → hom A C)

module category-structure (𝓒 : category-structure 𝓤 𝓥) where
 ob : 𝓤 ̇
 ob = pr₁ 𝓒

 hom : ob → ob → 𝓥 ̇
 hom A B = pr₁ (pr₂ 𝓒) A B

 idn : (A : ob) → hom A A
 idn A = pr₁ (pr₂ (pr₂ 𝓒)) A

 seq : {A B C : ob} (f : hom A B) (g : hom B C) → hom A C
 seq f g = pr₂ (pr₂ (pr₂ 𝓒)) _ _ _ f g

 cmp : {A B C : ob} (g : hom B C) (f : hom A B) → hom A C
 cmp f g = seq g f

module category-axiom-statements (𝓒 : category-structure 𝓤 𝓥) where
 open category-structure 𝓒

 statement-hom-is-set : 𝓤 ⊔ 𝓥 ̇
 statement-hom-is-set = (A B : ob) → is-set (hom A B)

 statement-idn-L : 𝓤 ⊔ 𝓥 ̇
 statement-idn-L = (A B : ob) (f : hom A B) → seq (idn A) f ＝ f

 statement-idn-R : 𝓤 ⊔ 𝓥 ̇
 statement-idn-R = (A B : ob) (f : hom A B) → seq f (idn B) ＝ f

 statement-assoc : 𝓤 ⊔ 𝓥 ̇
 statement-assoc =
  (A B C D : ob) (f : hom A B) (g : hom B C) (h : hom C D)
  → seq f (seq g h) ＝ seq (seq f g) h


 statement-hom-is-set-is-prop : is-prop statement-hom-is-set
 statement-hom-is-set-is-prop =
  Π-is-prop fe λ _ →
  Π-is-prop fe λ _ →
  being-set-is-prop fe

 module _ (hom-is-set : statement-hom-is-set) where
  statement-idn-L-is-prop : is-prop statement-idn-L
  statement-idn-L-is-prop =
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   hom-is-set _ _

  statement-idn-R-is-prop : is-prop statement-idn-R
  statement-idn-R-is-prop =
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   hom-is-set _ _

  statement-assoc-is-prop : is-prop statement-assoc
  statement-assoc-is-prop =
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   hom-is-set _ _

 -- TODO: univalence statement

-- Precategories are an intermediate notion in univalent 1-category theory.
module _ (𝓒 : category-structure 𝓤 𝓥) where
 open category-axiom-statements 𝓒

 precategory-axioms : 𝓤 ⊔ 𝓥 ̇
 precategory-axioms =
  statement-hom-is-set
  × statement-idn-L
  × statement-idn-R
  × statement-assoc

 precategory-axioms-is-prop : is-prop precategory-axioms
 precategory-axioms-is-prop =
  Σ-is-prop statement-hom-is-set-is-prop λ hom-is-set →
  ×-is-prop
   (statement-idn-L-is-prop hom-is-set)
   (×-is-prop
    (statement-idn-R-is-prop hom-is-set)
    (statement-assoc-is-prop hom-is-set))


 module precategory-axioms (ax : precategory-axioms) where
  hom-is-set : statement-hom-is-set
  hom-is-set = pr₁ ax

  idn-L : statement-idn-L
  idn-L = pr₁ (pr₂ ax)

  idn-R : statement-idn-R
  idn-R = pr₁ (pr₂ (pr₂ ax))

  assoc : statement-assoc
  assoc = pr₂ (pr₂ (pr₂ ax))

record precategory (𝓤 𝓥 : Universe) : (𝓤 ⊔ 𝓥)⁺ ̇ where
 constructor make
 field
  str : category-structure 𝓤 𝓥
  ax : precategory-axioms str

 open category-structure str public
 open precategory-axioms str ax public

module precategory-as-sum {𝓤 𝓥} where
 to-sum : precategory 𝓤 𝓥 → (Σ 𝓒 ꞉ category-structure 𝓤 𝓥 , precategory-axioms 𝓒)
 to-sum 𝓒 = let open precategory 𝓒 in str , ax

 from-sum : (Σ 𝓒 ꞉ category-structure 𝓤 𝓥 , precategory-axioms 𝓒) → precategory 𝓤 𝓥
 from-sum 𝓒 = make (pr₁ 𝓒) (pr₂ 𝓒)

 to-sum-is-equiv : is-equiv to-sum
 pr₁ (pr₁ to-sum-is-equiv) = from-sum
 pr₂ (pr₁ to-sum-is-equiv) _ = refl
 pr₁ (pr₂ to-sum-is-equiv) = from-sum
 pr₂ (pr₂ to-sum-is-equiv) _ = refl

module _ (𝓒 : precategory 𝓤 𝓥) where
 open precategory 𝓒

 module hom-properties {A B : ob} (f : hom A B) where

  module _ (g : hom B A) where
   is-inverse : 𝓥 ̇
   is-inverse = (seq f g ＝ idn A) × (seq g f ＝ idn B)

   being-inverse-is-prop : is-prop is-inverse
   being-inverse-is-prop = ×-is-prop (hom-is-set _ _) (hom-is-set _ _)

  inverse-is-unique
   : (g g' : hom B A)
   → is-inverse g
   → is-inverse g'
   → g ＝ g'
  inverse-is-unique g g' fg fg' =
   g ＝⟨ idn-R _ _ _ ⁻¹ ⟩
   seq g (idn _) ＝⟨ ap (seq g) (pr₁ fg' ⁻¹) ⟩
   seq g (seq f g') ＝⟨ assoc _ _ _ _ _ _ _ ⟩
   seq (seq g f) g' ＝⟨ ap (λ x → seq x g') (pr₂ fg) ⟩
   seq (idn _) g' ＝⟨ idn-L _ _ _ ⟩
   g' ∎

  is-iso : 𝓥 ̇
  is-iso = Σ g ꞉ hom B A , is-inverse g

  is-iso-is-prop : is-prop is-iso
  is-iso-is-prop (g , fg) (g' , fg') =
   to-Σ-＝
    (inverse-is-unique g g' fg fg' ,
     being-inverse-is-prop _ _ _)

 iso : ob → ob → 𝓥 ̇
 iso A B = Σ f ꞉ hom A B , hom-properties.is-iso f

 idn-is-iso : {A : ob} → hom-properties.is-iso (idn A)
 pr₁ idn-is-iso = idn _
 pr₁ (pr₂ idn-is-iso) = idn-L _ _ _
 pr₂ (pr₂ idn-is-iso) = idn-L _ _ _

 module _ (A B : ob) where
  ＝-to-iso : A ＝ B → iso A B
  ＝-to-iso refl = idn A , idn-is-iso

 is-univalent-precategory : 𝓤 ⊔ 𝓥 ̇
 is-univalent-precategory = (A B : ob) → is-equiv (＝-to-iso A B)

 being-univalent-is-prop : is-prop is-univalent-precategory
 being-univalent-is-prop =
  Π-is-prop fe λ _ →
  Π-is-prop fe λ _ →
  being-equiv-is-prop (λ _ _ → fe) _

category : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
category 𝓤 𝓥 = Σ 𝓒 ꞉ precategory 𝓤 𝓥 , is-univalent-precategory 𝓒

category-to-precategory : category 𝓤 𝓥 → precategory 𝓤 𝓥
category-to-precategory 𝓒 = pr₁ 𝓒

\end{code}
