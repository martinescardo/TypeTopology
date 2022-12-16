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

record deductive-system (𝓤 𝓥 : Universe) : (𝓤 ⊔ 𝓥) ⁺ ̇ where
 field
   ob : 𝓤 ̇
   _⊢_ : ob → ob → 𝓥 ̇
   ⊢-is-set : (A B : ob) → is-set (A ⊢ B)
   idn : (A : ob) → A ⊢ A
   cut : {A B C : ob} (f : A ⊢ B) (g : B ⊢ C) → A ⊢ C
   idn-L : (A B : ob) (f : A ⊢ B) → cut (idn A) f ＝ f
   idn-R : (A B : ob) (f : A ⊢ B) → cut f (idn B) ＝ f

 module _ {A B : ob} (f : A ⊢ B) where
  is-thunkable : 𝓤 ⊔ 𝓥  ̇
  is-thunkable =
   (C D : ob) (g : B ⊢ C) (h : C ⊢ D)
   → cut (cut f g) h ＝ cut f (cut g h)

  is-linear : 𝓤 ⊔ 𝓥 ̇
  is-linear =
   (U V : ob) (g : V ⊢ A) (h : U ⊢ V)
   → cut (cut h g) f ＝ (cut h (cut g f))

 module _ (A : ob) where
  is-positive : 𝓤 ⊔ 𝓥 ̇
  is-positive =
   (B : ob) (f : A ⊢ B)
   → is-linear f

  is-negative : 𝓤 ⊔ 𝓥 ̇
  is-negative =
   (B : ob) (f : B ⊢ A)
   → is-thunkable f

 are-inverse : {A B : ob} (f : A ⊢ B) (g : B ⊢ A) → 𝓥 ̇
 are-inverse f g = (cut f g ＝ idn _) × (cut g f ＝ idn _)

 module _ {A B} {f : A ⊢ B} where

  are-inverse-is-prop
   : {g : B ⊢ A}
   → is-prop (are-inverse f g)
  are-inverse-is-prop =
   ×-is-prop (⊢-is-set _ _) (⊢-is-set _ _)

  module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥)) (fe1 : funext 𝓥 𝓥) where
   is-thunkable-is-prop : is-prop (is-thunkable f)
   is-thunkable-is-prop =
    Π-is-prop fe0 λ C →
    Π-is-prop (lower-funext 𝓤 𝓤 fe0) λ D →
    Π-is-prop fe1 λ g →
    Π-is-prop fe1 λ h →
    ⊢-is-set _ _

   is-linear-is-prop : is-prop (is-linear f)
   is-linear-is-prop =
    Π-is-prop fe0 λ _ →
    Π-is-prop (lower-funext 𝓤 𝓤 fe0) λ _ →
    Π-is-prop fe1 λ _ →
    Π-is-prop fe1 λ _ →
    ⊢-is-set _ _

 module _ {A} (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥)) (fe1 : funext 𝓥 (𝓤 ⊔ 𝓥)) where
  is-positive-is-prop : is-prop (is-positive A)
  is-positive-is-prop =
   Π-is-prop fe0 λ _ →
   Π-is-prop fe1 λ _ →
   is-linear-is-prop fe0 (lower-funext 𝓥 𝓤 fe1)

  is-negative-is-prop : is-prop (is-negative A)
  is-negative-is-prop =
   Π-is-prop fe0 λ _ →
   Π-is-prop fe1 λ _ →
   is-thunkable-is-prop fe0 (lower-funext 𝓥 𝓤 fe1)


 module _ {A B} {f : A ⊢ B} {g g'} (fg : are-inverse f g) (fg' : are-inverse f g') where
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




\end{code}
