Jon Sterling, started 27th Sep 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Machines.DeductiveSystem where

open import UF.FunExt
open import UF.Base
open import UF.Equiv
open import UF.PropTrunc

open import MLTT.Spartan
open import UF.Base
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Logic
open import UF.Lower-FunExt

open import Categories.Precategory

deductive-system-structure : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
deductive-system-structure 𝓤 𝓥 = category-structure 𝓤 𝓥

module deductive-system-structure (𝓓 : deductive-system-structure 𝓤 𝓥) where
 ob : 𝓤 ̇
 ob = pr₁ 𝓓

 _⊢_ : ob → ob → 𝓥 ̇
 A ⊢ B = pr₁ (pr₂ 𝓓) A B

 idn : (A : ob) → A ⊢ A
 idn A = pr₁ (pr₂ (pr₂ 𝓓)) A

 cut : {A B C : ob} (f : A ⊢ B) (g : B ⊢ C) → A ⊢ C
 cut f g = pr₂ (pr₂ (pr₂ 𝓓)) f g

module _ (𝓓 : deductive-system-structure 𝓤 𝓥) where
 open deductive-system-structure 𝓓
 open category-axiom-statements 𝓓

 deductive-system-axioms : 𝓤 ⊔ 𝓥 ̇
 deductive-system-axioms =
  statement-hom-is-set
  × statement-idn-L
  × statement-idn-R

 module deductive-system-axioms (ax : deductive-system-axioms) where
  ⊢-is-set : statement-hom-is-set
  ⊢-is-set = pr₁ ax

  idn-L : statement-idn-L
  idn-L = pr₁ (pr₂ ax)

  idn-R : statement-idn-R
  idn-R = pr₂ (pr₂ ax)

deductive-system : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
deductive-system 𝓤 𝓥 =
 Σ 𝓓 ꞉ deductive-system-structure 𝓤 𝓥 ,
 deductive-system-axioms 𝓓

module deductive-system (𝓓 : deductive-system 𝓤 𝓥) where
 open deductive-system-structure (pr₁ 𝓓) public
 open deductive-system-axioms (pr₁ 𝓓) (pr₂ 𝓓) public

module ⊢-properties (𝓓 : deductive-system 𝓤 𝓥) where
 open deductive-system 𝓓

 module _ {A B : ob} (f : A ⊢ B) where
  is-thunkable : 𝓤 ⊔ 𝓥  ̇
  is-thunkable =
   (C D : ob) (g : B ⊢ C) (h : C ⊢ D)
   → cut (cut f g) h ＝ cut f (cut g h)

  is-linear : 𝓤 ⊔ 𝓥 ̇
  is-linear =
   (U V : ob) (g : V ⊢ A) (h : U ⊢ V)
   → cut (cut h g) f ＝ (cut h (cut g f))

  is-inverse : (g : B ⊢ A) → 𝓥 ̇
  is-inverse g = (cut f g ＝ idn _) × (cut g f ＝ idn _)

  being-inverse-is-prop
   : {g : B ⊢ A}
   → is-prop (is-inverse g)
  being-inverse-is-prop =
   ×-is-prop (⊢-is-set _ _) (⊢-is-set _ _)


 module _ {A B} {f : A ⊢ B} (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥)) (fe1 : funext 𝓥 𝓥) where
  being-thunkable-is-prop : is-prop (is-thunkable f)
  being-thunkable-is-prop =
   Π-is-prop fe0 λ C →
   Π-is-prop (lower-funext 𝓤 𝓤 fe0) λ D →
   Π-is-prop fe1 λ g →
   Π-is-prop fe1 λ h →
   ⊢-is-set _ _

  being-linear-is-prop : is-prop (is-linear f)
  being-linear-is-prop =
   Π-is-prop fe0 λ _ →
   Π-is-prop (lower-funext 𝓤 𝓤 fe0) λ _ →
   Π-is-prop fe1 λ _ →
   Π-is-prop fe1 λ _ →
   ⊢-is-set _ _

 module _ {A B} {f : A ⊢ B} {g g'} (fg : is-inverse f g) (fg' : is-inverse f g') where
  linear-inverse-is-unique
   : is-linear g
   → g' ＝ g
  linear-inverse-is-unique g-lin =
   g' ＝⟨ idn-R B A _ ⁻¹ ⟩
   cut _ (idn _) ＝⟨ ap (cut _) (pr₁ fg ⁻¹) ⟩
   cut _ (cut f _) ＝⟨ g-lin B A f _ ⁻¹ ⟩
   cut (cut _ f) _ ＝⟨ ap (λ x → cut x g) (pr₂ fg') ⟩
   cut (idn _) g ＝⟨ idn-L B A g ⟩
   g ∎

  thunkable-inverse-is-unique
   : is-thunkable g
   → g' ＝ g
  thunkable-inverse-is-unique g-th =
   g' ＝⟨ idn-L B A g' ⁻¹ ⟩
   cut (idn _) g' ＝⟨ ap (λ x → cut x g') (pr₂ fg ⁻¹) ⟩
   cut (cut g f) g' ＝⟨ g-th B A f g' ⟩
   cut g (cut f g') ＝⟨ ap (cut g) (pr₁ fg') ⟩
   cut g (idn _) ＝⟨ idn-R B A g ⟩
   g ∎


module polarities (𝓓 : deductive-system 𝓤 𝓥) where
 open deductive-system 𝓓
 open ⊢-properties 𝓓

 module _ (A : ob) where
  is-positive : 𝓤 ⊔ 𝓥 ̇
  is-positive =
   (B : ob) (f : A ⊢ B)
   → is-linear f

  is-negative : 𝓤 ⊔ 𝓥 ̇
  is-negative =
   (B : ob) (f : B ⊢ A)
   → is-thunkable f

 module _ {A} (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥)) (fe1 : funext 𝓥 (𝓤 ⊔ 𝓥)) where
  private
   fe2 : funext 𝓥 𝓥
   fe2 = lower-funext 𝓥 𝓤 fe1

  being-positive-is-prop : is-prop (is-positive A)
  being-positive-is-prop =
   Π-is-prop fe0 λ _ →
   Π-is-prop fe1 λ _ →
   being-linear-is-prop fe0 fe2

  being-negative-is-prop : is-prop (is-negative A)
  being-negative-is-prop =
   Π-is-prop fe0 λ _ →
   Π-is-prop fe1 λ _ →
   being-thunkable-is-prop fe0 fe2

\end{code}
