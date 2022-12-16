Jon Sterling, started 28th Sep 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Categories.Precategory where

open import MLTT.Spartan
open import UF.FunExt
open import UF.Base
open import UF.Equiv
open import UF.Lower-FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Equiv-FunExt

-- We prefer composition in diagrammatic order.

category-structure : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
category-structure 𝓤 𝓥 =
 Σ ob ꞉ (𝓤 ̇),
 Σ hom ꞉ (ob → ob → 𝓥 ̇) ,
 Σ idn ꞉ ((A : ob) → hom A A) ,
 ({A B C : ob} (f : hom A B) (g : hom B C) → hom A C)

module category-structure (𝓒 : category-structure 𝓤 𝓥) where
 ob : 𝓤 ̇
 ob = pr₁ 𝓒

 hom : ob → ob → 𝓥 ̇
 hom A B = pr₁ (pr₂ 𝓒) A B

 idn : (A : ob) → hom A A
 idn A = pr₁ (pr₂ (pr₂ 𝓒)) A

 seq : {A B C : ob} (f : hom A B) (g : hom B C) → hom A C
 seq f g = pr₂ (pr₂ (pr₂ 𝓒)) f g

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


 module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥)) (fe1 : funext 𝓥 𝓥) where
  private
   fe2 : funext 𝓤 𝓥
   fe2 = lower-funext 𝓤 𝓤 fe0

  statement-hom-is-set-is-prop : is-prop statement-hom-is-set
  statement-hom-is-set-is-prop =
   Π-is-prop fe0 λ _ →
   Π-is-prop fe2 λ _ →
   being-set-is-prop fe1

  module _ (hom-is-set : statement-hom-is-set) where
   statement-idn-L-is-prop : is-prop statement-idn-L
   statement-idn-L-is-prop =
    Π-is-prop fe0 λ _ →
    Π-is-prop fe2 λ _ →
    Π-is-prop fe1 λ _ →
    hom-is-set _ _

   statement-idn-R-is-prop : is-prop statement-idn-R
   statement-idn-R-is-prop =
    Π-is-prop fe0 λ _ →
    Π-is-prop fe2 λ _ →
    Π-is-prop fe1 λ _ →
    hom-is-set _ _

   statement-assoc-is-prop : is-prop statement-assoc
   statement-assoc-is-prop =
    Π-is-prop fe0 λ _ →
    Π-is-prop fe0 λ _ →
    Π-is-prop fe0 λ _ →
    Π-is-prop fe2 λ _ →
    Π-is-prop fe1 λ _ →
    Π-is-prop fe1 λ _ →
    Π-is-prop fe1 λ _ →
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

 module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥)) (fe1 : funext 𝓥 𝓥) where
  precategory-axioms-is-prop : is-prop precategory-axioms
  precategory-axioms-is-prop =
   Σ-is-prop (statement-hom-is-set-is-prop fe0 fe1) λ hom-is-set →
   ×-is-prop
    (statement-idn-L-is-prop fe0 fe1 hom-is-set)
    (×-is-prop
     (statement-idn-R-is-prop fe0 fe1 hom-is-set)
     (statement-assoc-is-prop fe0 fe1 hom-is-set))


 module precategory-axioms (ax : precategory-axioms) where
  hom-is-set : statement-hom-is-set
  hom-is-set = pr₁ ax

  idn-L : statement-idn-L
  idn-L = pr₁ (pr₂ ax)

  idn-R : statement-idn-R
  idn-R = pr₁ (pr₂ (pr₂ ax))

  assoc : statement-assoc
  assoc = pr₂ (pr₂ (pr₂ ax))

precategory : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
precategory 𝓤 𝓥 =
 Σ 𝓒 ꞉ category-structure 𝓤 𝓥 ,
 precategory-axioms 𝓒

module precategory (𝓒 : precategory 𝓤 𝓥) where
 open category-structure (pr₁ 𝓒) public
 open precategory-axioms (pr₁ 𝓒) (pr₂ 𝓒) public


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

 module precategory-univalence where
  module _ (A B : ob) where
   ＝-to-iso : A ＝ B → iso A B
   ＝-to-iso refl = idn A , idn-is-iso

  is-univalent : 𝓤 ⊔ 𝓥 ̇
  is-univalent = (A B : ob) → is-equiv (＝-to-iso A B)

  module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥)) (fe1 : funext 𝓥 𝓥) (fe2 : funext 𝓥 𝓤) where
   private
    fe3 : funext 𝓤 𝓤
    fe3 = lower-funext 𝓤 𝓥 fe0

   being-univalent-is-prop : is-prop is-univalent
   being-univalent-is-prop =
    Π-is-prop fe0 λ _ →
    Π-is-prop fe0 λ _ →
    being-equiv-is-prop' fe2 fe1 fe3 fe2 _


\end{code}
