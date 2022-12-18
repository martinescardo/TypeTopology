Jon Sterling, started 16th Dec 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Categories.NaturalTransformation where

open import MLTT.Spartan
open import UF.FunExt
open import UF.Base
open import UF.Equiv
open import UF.Lower-FunExt
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Equiv-FunExt

open import Categories.Category
open import Categories.Functor

module natural-transformation (𝓒 : precategory 𝓤 𝓥) (𝓓 : precategory 𝓤' 𝓥') where
 private
  module 𝓒 = precategory 𝓒
  module 𝓓 = precategory 𝓓

 open functor-of-precategories 𝓒 𝓓

 module _ (F G : functor) where
  private
   module F = functor F
   module G = functor G

  transf : 𝓤 ⊔ 𝓥' ̇
  transf = (A : 𝓒.ob) → 𝓓.hom (F.ob A) (G.ob A)

  transf-is-set : (fe : funext 𝓤 𝓥') → is-set transf
  transf-is-set fe =
   Π-is-set fe λ _ →
   𝓓.hom-is-set (F.ob _) (G.ob _)

  is-natural : transf → 𝓤 ⊔ 𝓥 ⊔ 𝓥' ̇
  is-natural α =
   (A B : 𝓒.ob) (f : 𝓒.hom A B)
   → 𝓓.seq (F.hom f) (α B) ＝ 𝓓.seq (α A) (G.hom f)

  nat-transf : 𝓤 ⊔ 𝓥 ⊔ 𝓥' ̇
  nat-transf = Σ α ꞉ transf , is-natural α

  module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥 ⊔ 𝓥')) (fe1 : funext 𝓥 𝓥')  where
    private
     fe2 : funext 𝓤 (𝓥 ⊔ 𝓥')
     fe2 = lower-funext 𝓤 𝓤 fe0

     fe3 : funext 𝓤 𝓥'
     fe3 = lower-funext 𝓤 (𝓤 ⊔ 𝓥) fe0

    being-natural-is-prop : {α : transf} → is-prop (is-natural α)
    being-natural-is-prop =
     Π-is-prop fe0 λ _ →
     Π-is-prop fe2 λ _ →
     Π-is-prop fe1 λ _ →
     𝓓.hom-is-set _ _

    nat-transf-is-set : is-set nat-transf
    nat-transf-is-set =
     Σ-is-set (transf-is-set fe3) λ _ →
     props-are-sets being-natural-is-prop

    module _ {α β : nat-transf} where
     to-nat-transf-＝ : pr₁ α ＝ pr₁ β → α ＝ β
     to-nat-transf-＝ h = to-Σ-＝ (h , being-natural-is-prop _ _)

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

 module _ (F G : functor) (α : transf F G) (fe : funext 𝓤 𝓥') where
  transf-idn-L : transf-seq F F G (transf-idn F) α ＝ α
  transf-idn-L =
   dfunext fe λ _ →
   𝓓.idn-L _ _ _

  transf-idn-R : transf-seq F G G α (transf-idn G) ＝ α
  transf-idn-R =
   dfunext fe λ _ →
   𝓓.idn-R _ _ _

 module _
  (F G H I : functor)
  (α : transf F G)
  (β : transf G H)
  (γ : transf H I)
  (fe : funext 𝓤 𝓥')
  where
  transf-assoc
   : transf-seq F G I α (transf-seq G H I β γ)
   ＝ transf-seq F H I (transf-seq F G H α β) γ
  transf-assoc =
   dfunext fe λ _ →
   𝓓.assoc _ _ _ _ _ _ _

 module nat-transf-laws (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥 ⊔ 𝓥')) (fe1 : funext 𝓥 𝓥') where
  private
   fe2 : funext 𝓤 𝓥'
   fe2 = lower-funext 𝓤 (𝓤 ⊔ 𝓥) fe0

  module _ (F G : functor) (α : nat-transf F G) where
   nat-transf-idn-L : nat-transf-seq F F G (nat-transf-idn F) α ＝ α
   nat-transf-idn-L =
    to-nat-transf-＝ F G fe0 fe1
     (transf-idn-L F G (pr₁ α) fe2)

   nat-transf-idn-R : nat-transf-seq F G G α (nat-transf-idn G) ＝ α
   nat-transf-idn-R =
    to-nat-transf-＝ F G fe0 fe1
     (transf-idn-R F G (pr₁ α) fe2)

  module _ (F G H I : functor) (α : nat-transf F G) (β : nat-transf G H) (γ : nat-transf H I) where
   nat-transf-assoc
    : nat-transf-seq F G I α (nat-transf-seq G H I β γ)
    ＝ nat-transf-seq F H I (nat-transf-seq F G H α β) γ
   nat-transf-assoc =
    to-nat-transf-＝ F I fe0 fe1
     (transf-assoc F G H I (pr₁ α) (pr₁ β) (pr₁ γ) fe2)

 module functor-category where
  structure : category-structure (𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥') (𝓤 ⊔ 𝓥 ⊔ 𝓥')
  structure = functor , nat-transf , nat-transf-idn , nat-transf-seq

  module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥 ⊔ 𝓥')) (fe1 : funext 𝓥 𝓥') where
   axioms : precategory-axioms structure
   axioms =
    let open nat-transf-laws fe0 fe1 in
    (λ F G → nat-transf-is-set F G fe0 fe1) ,
    nat-transf-idn-L ,
    nat-transf-idn-R ,
    nat-transf-assoc

   precat : precategory (𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥') (𝓤 ⊔ 𝓥 ⊔ 𝓥')
   precat = structure , axioms

\end{code}
