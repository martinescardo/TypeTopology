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

 module _ (F : functor) where
  private module F = functor F
  transf-idn : transf F F
  transf-idn A = 𝓓.idn (F.ob A)

  abstract
   transf-idn-natural : is-natural F F transf-idn
   transf-idn-natural A B f =
    𝓓.seq (F.hom f) (𝓓.idn _) ＝⟨ 𝓓.idn-R _ _ _ ⟩
    F.hom f ＝⟨ 𝓓.idn-L _ _ _ ⁻¹ ⟩
    𝓓.seq (𝓓.idn _) (F.hom f) ∎

  nat-transf-idn : nat-transf F F
  nat-transf-idn = transf-idn , transf-idn-natural

 module _ (F G H : functor) where
  private
   module F = functor F
   module G = functor G
   module H = functor H

  module _ (α : transf F G) (β : transf G H) where
   transf-seq : transf F H
   transf-seq A = 𝓓.seq (α A) (β A)

   module _ (α-nat : is-natural F G α) (β-nat : is-natural G H β) where
    abstract
     transf-seq-natural : is-natural F H transf-seq
     transf-seq-natural A B f =
      𝓓.seq (F.hom f) (𝓓.seq (α B) (β B))
       ＝⟨ 𝓓.assoc _ _ _ _ _ _ _ ⟩
      𝓓.seq (𝓓.seq (F.hom f) (α B)) (β B)
       ＝⟨ ap (λ x → 𝓓.seq x (β B)) (α-nat _ _ _) ⟩
      𝓓.seq (𝓓.seq (α A) (G.hom f)) (β B)
       ＝⟨ 𝓓.assoc _ _ _ _ _ _ _ ⁻¹ ⟩
      𝓓.seq (α A) (𝓓.seq (G.hom f) (β B))
       ＝⟨ ap (𝓓.seq (α A)) (β-nat _ _ _) ⟩
      𝓓.seq (α A) (𝓓.seq (β A) (H.hom f))
       ＝⟨ 𝓓.assoc _ _ _ _ _ _ _ ⟩
      𝓓.seq (𝓓.seq (α A) (β A)) (H.hom f) ∎

  nat-transf-seq : nat-transf F G  → nat-transf G H → nat-transf F H
  pr₁ (nat-transf-seq α β) = transf-seq (pr₁ α) (pr₁ β)
  pr₂ (nat-transf-seq α β) = transf-seq-natural (pr₁ α) (pr₁ β) (pr₂ α) (pr₂ β)

 module functor-category where
  structure : category-structure (𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥') (𝓤 ⊔ 𝓥 ⊔ 𝓥')
  structure = functor , nat-transf , nat-transf-idn , nat-transf-seq

\end{code}
