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

module _ (𝓒 : precategory 𝓣 𝓤) (𝓓 : precategory 𝓣' 𝓤') (𝓔 : precategory 𝓥 𝓦) where
 private
  module 𝓒 = precategory 𝓒
  module 𝓓 = precategory 𝓓
  module 𝓔 = precategory 𝓔
 open functor-of-precategories
 open natural-transformation

 module horizontal-composition
  (F1 G1 : functor 𝓒 𝓓)
  (F2 G2 : functor 𝓓 𝓔)
  (α : nat-transf 𝓒 𝓓 F1 G1)
  (β : nat-transf 𝓓 𝓔 F2 G2)
  where

  private
   F3 = composite-functor.fun 𝓒 𝓓 𝓔 F1 F2
   G3 = composite-functor.fun 𝓒 𝓓 𝓔 G1 G2
   module F1 = functor 𝓒 𝓓 F1
   module F2 = functor 𝓓 𝓔 F2
   module G1 = functor 𝓒 𝓓 G1
   module G2 = functor 𝓓 𝓔 G2
   module F3 = functor 𝓒 𝓔 F3
   module G3 = functor 𝓒 𝓔 G3

  hcomp-str : transf 𝓒 𝓔 F3 G3
  hcomp-str A = 𝓔.seq (pr₁ β (F1.ob A)) (G2.hom (pr₁ α A))

  abstract
   hcomp-ax : is-natural 𝓒 𝓔 F3 G3 hcomp-str
   hcomp-ax A B f =
    𝓔.seq (F2.hom (F1.hom f)) (𝓔.seq (pr₁ β (F1.ob B)) (G2.hom (pr₁ α B)))
     ＝⟨ 𝓔.assoc _ _ _ _ _ _ _ ⟩
    𝓔.seq (𝓔.seq (F3.hom f) (pr₁ β (F1.ob B))) (G2.hom (pr₁ α B))
     ＝⟨ ap (λ x → 𝓔.seq x _) h0 ⟩
    𝓔.seq (𝓔.seq (pr₁ β (F1.ob A)) (G2.hom (F1.hom f))) (G2.hom (pr₁ α B))
     ＝⟨ 𝓔.assoc _ _ _ _ _ _ _ ⁻¹ ⟩
    𝓔.seq (pr₁ β (F1.ob A)) (𝓔.seq (G2.hom (F1.hom f)) (G2.hom (pr₁ α B)))
     ＝⟨ ap (𝓔.seq (pr₁ β (F1.ob A))) h1 ⟩
    𝓔.seq (pr₁ β (F1.ob A)) (𝓔.seq (G2.hom (pr₁ α A)) (G3.hom f))
     ＝⟨ 𝓔.assoc _ _ _ _ _ _ _ ⟩
    𝓔.seq (𝓔.seq (pr₁ β (F1.ob A)) (G2.hom (pr₁ α A))) (G3.hom f) ∎
    where
     h0
      : 𝓔.seq (F2.hom (F1.hom f)) (pr₁ β (F1.ob B))
      ＝ 𝓔.seq (pr₁ β (F1.ob A)) (G2.hom (F1.hom f))
     h0 = pr₂ β (F1.ob A) (F1.ob B) (F1.hom f)

     h1
      : 𝓔.seq (G2.hom (F1.hom f)) (G2.hom (pr₁ α B))
      ＝ 𝓔.seq (G2.hom (pr₁ α A)) (G3.hom f)
     h1 =
      𝓔.seq (G2.hom (F1.hom f)) (G2.hom (pr₁ α B))
       ＝⟨ G2.preserves-seq _ _ _ _ _ ⁻¹ ⟩
      G2.hom (𝓓.seq (F1.hom f) (pr₁ α B))
       ＝⟨ ap G2.hom (pr₂ α _ _ _) ⟩
      G2.hom (𝓓.seq (pr₁ α A) (G1.hom f))
       ＝⟨ G2.preserves-seq _ _ _ _ _ ⟩
      𝓔.seq (G2.hom (pr₁ α A)) (G3.hom f) ∎

  hcomp : nat-transf 𝓒 𝓔 F3 G3
  hcomp = hcomp-str , hcomp-ax


 module left-whiskering
  (W : functor 𝓒 𝓓)
  (G H : functor 𝓓 𝓔)
  (β : nat-transf 𝓓 𝓔 G H)
  where

  private
   G∘W = composite-functor.fun 𝓒 𝓓 𝓔 W G
   H∘W = composite-functor.fun 𝓒 𝓓 𝓔 W H

  open horizontal-composition W W G H (nat-transf-idn 𝓒 𝓓 W) β

  whisk : nat-transf 𝓒 𝓔 G∘W H∘W
  whisk = hcomp

 module right-whiskering
  (G H : functor 𝓒 𝓓)
  (W : functor 𝓓 𝓔)
  (β : nat-transf 𝓒 𝓓 G H)
  where

  private
   W∘G = composite-functor.fun 𝓒 𝓓 𝓔 G W
   W∘H = composite-functor.fun 𝓒 𝓓 𝓔 H W

  open horizontal-composition G H W W β (nat-transf-idn 𝓓 𝓔 W)

  whisk : nat-transf 𝓒 𝓔 W∘G W∘H
  whisk = hcomp

\end{code}
