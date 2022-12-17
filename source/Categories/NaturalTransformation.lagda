Jon Sterling, started 16th Dec 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Categories.NaturalTransformation where

open import MLTT.Spartan
open import UF.FunExt
open import UF.Base
open import UF.Equiv
open import UF.Lower-FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Equiv-FunExt

open import Categories.Category
open import Categories.Functor

module _ {𝓒 : precategory 𝓤 𝓥} {𝓓 : precategory 𝓤' 𝓥'} where
 module 𝓒 = precategory 𝓒
 module 𝓓 = precategory 𝓓
 open functor-of-precategories 𝓒 𝓓

 module _ (F G : functor) where
  private
   module F = functor F
   module G = functor G

  transf : 𝓤 ⊔ 𝓥' ̇
  transf = (A : 𝓒.ob) → 𝓓.hom (F.ob A) (G.ob A)

  module _ (α : transf) where
   is-natural : 𝓤 ⊔ 𝓥 ⊔ 𝓥' ̇
   is-natural =
    (A B : 𝓒.ob) (f : 𝓒.hom A B)
    → 𝓓.seq (F.hom f) (α B) ＝ 𝓓.seq (α A) (G.hom f)

   module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥 ⊔ 𝓥')) (fe1 : funext 𝓥 𝓥')  where
    private
     fe2 : funext 𝓤 (𝓥 ⊔ 𝓥')
     fe2 = lower-funext 𝓤 𝓤 fe0

    being-natural-is-prop : is-prop is-natural
    being-natural-is-prop =
     Π-is-prop fe0 λ _ →
     Π-is-prop fe2 λ _ →
     Π-is-prop fe1 λ _ →
     𝓓.hom-is-set _ _

  nat-transf : 𝓤 ⊔ 𝓥 ⊔ 𝓥' ̇
  nat-transf = Σ α ꞉ transf , is-natural α

  -- TODO : characterize identity type

 module functor-category where
  module str where
   ob : 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇
   ob = functor

   hom : ob → ob → 𝓤 ⊔ 𝓥 ⊔ 𝓥' ̇
   hom = nat-transf

   idn : (F : ob) → hom F F
   pr₁ (idn F) A = 𝓓.idn (functor.ob F A)
   pr₂ (idn F) A B f =
    let module F = functor F in
    𝓓.seq (F.hom f) (𝓓.idn _) ＝⟨ 𝓓.idn-R _ _ _ ⟩
    F.hom f ＝⟨ 𝓓.idn-L _ _ _ ⁻¹ ⟩
    𝓓.seq (𝓓.idn _) (F.hom f) ∎

   module _ (F G H : ob) where
    private
     module F = functor F
     module G = functor G
     module H = functor H

    seq : hom F G → hom G H → hom F H
    pr₁ (seq α β) A = 𝓓.seq (pr₁ α A) (pr₁ β A)
    pr₂ (seq α β) A B f =
     𝓓.seq (F.hom f) (𝓓.seq (pr₁ α B) (pr₁ β B))
      ＝⟨ 𝓓.assoc _ _ _ _ _ _ _ ⟩
     𝓓.seq (𝓓.seq (F.hom f) (pr₁ α B)) (pr₁ β B)
      ＝⟨ ap (λ x → 𝓓.seq x (pr₁ β B)) (pr₂ α _ _ _) ⟩
     𝓓.seq (𝓓.seq (pr₁ α A) (G.hom f)) (pr₁ β B)
      ＝⟨ 𝓓.assoc _ _ _ _ _ _ _ ⁻¹ ⟩
     𝓓.seq (pr₁ α A) (𝓓.seq (G.hom f) (pr₁ β B))
      ＝⟨ ap (𝓓.seq (pr₁ α A)) (pr₂ β _ _ _) ⟩
     𝓓.seq (pr₁ α A) (𝓓.seq (pr₁ β A) (H.hom f))
      ＝⟨ 𝓓.assoc _ _ _ _ _ _ _ ⟩
     𝓓.seq (𝓓.seq (pr₁ α A) (pr₁ β A)) (H.hom f) ∎

   structure : category-structure (𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥') (𝓤 ⊔ 𝓥 ⊔ 𝓥')
   structure = ob , hom , idn , seq


\end{code}
