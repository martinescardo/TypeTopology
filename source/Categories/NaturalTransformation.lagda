Jon Sterling, started 16th Dec 2022

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Categories.NaturalTransformation (fe : Fun-Ext) where

open import Categories.Category fe
open import Categories.Functor fe
open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties

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

  transf-is-set : is-set transf
  transf-is-set  =
   Π-is-set fe λ _ →
   𝓓.hom-is-set (F.ob _) (G.ob _)

  is-natural : transf → 𝓤 ⊔ 𝓥 ⊔ 𝓥' ̇
  is-natural α =
   (A B : 𝓒.ob) (f : 𝓒.hom A B)
   → 𝓓.seq (F.hom f) (α B) ＝ 𝓓.seq (α A) (G.hom f)

  record nat-transf : 𝓤 ⊔ 𝓥 ⊔ 𝓥' ̇ where
   constructor make
   field
    str : transf
    ax : is-natural str

  module nat-transf-as-sum where
   to-sum : nat-transf → Σ is-natural
   to-sum α = let open nat-transf α in str , ax

   from-sum : Σ is-natural → nat-transf
   from-sum α = make (pr₁ α) (pr₂ α)

   to-sum-is-equiv : is-equiv to-sum
   pr₁ (pr₁ to-sum-is-equiv) = from-sum
   pr₂ (pr₁ to-sum-is-equiv) _ = refl
   pr₁ (pr₂ to-sum-is-equiv) = from-sum
   pr₂ (pr₂ to-sum-is-equiv) (make str ax) = refl

   equiv : nat-transf ≃ Σ is-natural
   equiv = to-sum , to-sum-is-equiv

  being-natural-is-prop : {α : transf} → is-prop (is-natural α)
  being-natural-is-prop =
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   𝓓.hom-is-set _ _

  nat-transf-is-set : is-set nat-transf
  nat-transf-is-set =
   equiv-to-set
    nat-transf-as-sum.equiv
    (Σ-is-set transf-is-set λ _ →
     props-are-sets being-natural-is-prop)

  module _ {α β : nat-transf} where
   to-nat-transf-＝ : nat-transf.str α ＝ nat-transf.str β → α ＝ β
   to-nat-transf-＝ h =
    equivs-are-lc
     nat-transf-as-sum.to-sum
     nat-transf-as-sum.to-sum-is-equiv
     (to-Σ-＝ (h , being-natural-is-prop _ _))

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
  nat-transf-idn = make transf-idn transf-idn-natural

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
  nat-transf-seq α β =
   let module α = nat-transf α in
   let module β = nat-transf β in
   make
    (transf-seq α.str β.str)
    (transf-seq-natural α.str β.str α.ax β.ax)

 module _ (F G : functor) (α : transf F G) where
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
  where
  transf-assoc
   : transf-seq F G I α (transf-seq G H I β γ)
   ＝ transf-seq F H I (transf-seq F G H α β) γ
  transf-assoc =
   dfunext fe λ _ →
   𝓓.assoc _ _ _ _ _ _ _

 module nat-transf-laws (F G : functor) (α : nat-transf F G) where
  module α = nat-transf α

  nat-transf-idn-L : nat-transf-seq _ _ _ (nat-transf-idn F) α ＝ α
  nat-transf-idn-L =
   to-nat-transf-＝ F G
    (transf-idn-L F G α.str)

  nat-transf-idn-R : nat-transf-seq _ _ _ α (nat-transf-idn G) ＝ α
  nat-transf-idn-R =
   to-nat-transf-＝ F G
    (transf-idn-R F G α.str)

 module _ (F G H I : functor) (α : nat-transf F G) (β : nat-transf G H) (γ : nat-transf H I) where
  nat-transf-assoc
   : nat-transf-seq _ _ _ α (nat-transf-seq _ _ _ β γ)
   ＝ nat-transf-seq _ _ _ (nat-transf-seq _ _ _ α β) γ
  nat-transf-assoc =
   to-nat-transf-＝ F I
    (transf-assoc F G H I _ _ _)

 module functor-category where
  structure : category-structure (𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥') (𝓤 ⊔ 𝓥 ⊔ 𝓥')
  structure = functor , nat-transf , nat-transf-idn , nat-transf-seq

  axioms : precategory-axioms structure
  axioms =
   let open nat-transf-laws in
   nat-transf-is-set ,
   nat-transf-idn-L ,
   nat-transf-idn-R ,
   nat-transf-assoc

  precat : precategory (𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥') (𝓤 ⊔ 𝓥 ⊔ 𝓥')
  precat = make structure axioms

module _ {𝓒 : precategory 𝓣 𝓤} {𝓓 : precategory 𝓣' 𝓤'} {𝓔 : precategory 𝓥 𝓦} where
 private
  module 𝓒 = precategory 𝓒
  module 𝓓 = precategory 𝓓
  module 𝓔 = precategory 𝓔

 open functor-of-precategories
 open natural-transformation

 module horizontal-composition
  {F1 G1 : functor 𝓒 𝓓}
  {F2 G2 : functor 𝓓 𝓔}
  (α : nat-transf 𝓒 𝓓 F1 G1)
  (β : nat-transf 𝓓 𝓔 F2 G2)
  where

  private
   F3 = composite-functor.fun F1 F2
   G3 = composite-functor.fun G1 G2
   module F1 = functor F1
   module F2 = functor F2
   module G1 = functor G1
   module G2 = functor G2
   module F3 = functor F3
   module G3 = functor G3
   module α = nat-transf α
   module β = nat-transf β

  hcomp-str : transf 𝓒 𝓔 F3 G3
  hcomp-str A = 𝓔.seq (β.str (F1.ob A)) (G2.hom (α.str A))

  abstract
   hcomp-ax : is-natural 𝓒 𝓔 F3 G3 hcomp-str
   hcomp-ax A B f =
    𝓔.seq (F2.hom (F1.hom f)) (𝓔.seq (β.str (F1.ob B)) (G2.hom (α.str B)))
     ＝⟨ 𝓔.assoc _ _ _ _ _ _ _ ⟩
    𝓔.seq (𝓔.seq (F3.hom f) (β.str (F1.ob B))) (G2.hom (α.str B))
     ＝⟨ ap (λ x → 𝓔.seq x _) h0 ⟩
    𝓔.seq (𝓔.seq (β.str (F1.ob A)) (G2.hom (F1.hom f))) (G2.hom (α.str B))
     ＝⟨ 𝓔.assoc _ _ _ _ _ _ _ ⁻¹ ⟩
    𝓔.seq (β.str (F1.ob A)) (𝓔.seq (G2.hom (F1.hom f)) (G2.hom (α.str B)))
     ＝⟨ ap (𝓔.seq (β.str (F1.ob A))) h1 ⟩
    𝓔.seq (β.str (F1.ob A)) (𝓔.seq (G2.hom (α.str A)) (G3.hom f))
     ＝⟨ 𝓔.assoc _ _ _ _ _ _ _ ⟩
    𝓔.seq (𝓔.seq (β.str (F1.ob A)) (G2.hom (α.str A))) (G3.hom f) ∎
    where
     h0
      : 𝓔.seq (F2.hom (F1.hom f)) (β.str (F1.ob B))
      ＝ 𝓔.seq (β.str (F1.ob A)) (G2.hom (F1.hom f))
     h0 = β.ax (F1.ob A) (F1.ob B) (F1.hom f)

     h1
      : 𝓔.seq (G2.hom (F1.hom f)) (G2.hom (α.str B))
      ＝ 𝓔.seq (G2.hom (α.str A)) (G3.hom f)
     h1 =
      𝓔.seq (G2.hom (F1.hom f)) (G2.hom (α.str B))
       ＝⟨ G2.preserves-seq _ _ _ _ _ ⁻¹ ⟩
      G2.hom (𝓓.seq (F1.hom f) (α.str B))
       ＝⟨ ap G2.hom (α.ax _ _ _) ⟩
      G2.hom (𝓓.seq (α.str A) (G1.hom f))
       ＝⟨ G2.preserves-seq _ _ _ _ _ ⟩
      𝓔.seq (G2.hom (α.str A)) (G3.hom f) ∎

  hcomp : nat-transf 𝓒 𝓔 F3 G3
  hcomp = make hcomp-str hcomp-ax

 module left-whiskering
  {G H : functor 𝓓 𝓔}
  (W : functor 𝓒 𝓓)
  (β : nat-transf 𝓓 𝓔 G H)
  where

  private
   W-G = composite-functor.fun W G
   W-H = composite-functor.fun W H
   module W = functor W
   module H = functor H
   module β = nat-transf β

  whisk-str : transf _ _ W-G W-H
  whisk-str A = β.str (W.ob A)

  whisk-ax : is-natural _ _ W-G W-H whisk-str
  whisk-ax A B f = β.ax (W.ob A) (W.ob B) (W.hom f)

  whisk : nat-transf _ _ W-G W-H
  whisk = make whisk-str whisk-ax

 module right-whiskering
  {G H : functor 𝓒 𝓓}
  (β : nat-transf _ _ G H)
  (W : functor 𝓓 𝓔)
  where

  private
   G-W = composite-functor.fun G W
   H-W = composite-functor.fun H W
   module W = functor W
   module G = functor G
   module H = functor H
   module β = nat-transf β

  whisk-str : transf _ _ G-W H-W
  whisk-str A = W.hom (β.str A)

  whisk-ax : is-natural _ _ G-W H-W whisk-str
  whisk-ax A B f =
   𝓔.seq (W.hom (G.hom f)) (W.hom (β.str B)) ＝⟨ W.preserves-seq _ _ _ _ _ ⁻¹ ⟩
   W.hom (𝓓.seq (G.hom f) (β.str B)) ＝⟨ ap W.hom (β.ax _ _ _) ⟩
   W.hom (𝓓.seq (β.str A) (H.hom f)) ＝⟨ W.preserves-seq _ _ _ _ _ ⟩
   𝓔.seq (W.hom (β.str A)) (W.hom (H.hom f)) ∎

  whisk : nat-transf 𝓒 𝓔 G-W H-W
  whisk = make whisk-str whisk-ax


module
 _
  {𝓒 : precategory 𝓣 𝓤} {𝓓 : precategory 𝓥 𝓦}
  (open functor-of-precategories)
  (F : functor 𝓒 𝓓)
 where
 open natural-transformation

 private
  module 𝓓 = precategory 𝓓
  module F = functor F
  1[𝓒] = identity-functor.fun 𝓒
  1[𝓓] = identity-functor.fun 𝓓
  1[𝓒]-F = composite-functor.fun 1[𝓒] F
  F-1[𝓓] = composite-functor.fun F 1[𝓓]
  [𝓒,𝓓] = functor-category.precat 𝓒 𝓓
  module [𝓒,𝓓] = precategory [𝓒,𝓓]

 left-unitor : [𝓒,𝓓].hom 1[𝓒]-F F
 nat-transf.str left-unitor A = 𝓓.idn (F.ob A)
 nat-transf.ax left-unitor A B f =
  𝓓.seq (F.hom f) (𝓓.idn (F.ob B)) ＝⟨ 𝓓.idn-R _ _ _ ⟩
  F.hom f ＝⟨ 𝓓.idn-L _ _ _ ⁻¹ ⟩
  𝓓.seq (𝓓.idn (F.ob A)) (F.hom f) ∎

 left-unitor-inverse : [𝓒,𝓓].hom F 1[𝓒]-F
 nat-transf.str left-unitor-inverse A = 𝓓.idn (F.ob A)
 nat-transf.ax left-unitor-inverse A B f =
  𝓓.seq (F.hom f) (𝓓.idn (F.ob B)) ＝⟨ 𝓓.idn-R _ _ _ ⟩
  F.hom f ＝⟨ 𝓓.idn-L _ _ _ ⁻¹ ⟩
  𝓓.seq (𝓓.idn (F.ob A)) (F.hom f) ∎

 right-unitor : [𝓒,𝓓].hom F-1[𝓓] F
 nat-transf.str right-unitor A = 𝓓.idn (F.ob A)
 nat-transf.ax right-unitor A B f =
  𝓓.seq (F.hom f) (𝓓.idn (F.ob B)) ＝⟨ 𝓓.idn-R _ _ _ ⟩
  F.hom f ＝⟨ 𝓓.idn-L _ _ _ ⁻¹ ⟩
  𝓓.seq (𝓓.idn (F.ob A)) (F.hom f) ∎

 right-unitor-inverse : [𝓒,𝓓].hom F F-1[𝓓]
 nat-transf.str right-unitor-inverse A = 𝓓.idn (F.ob A)
 nat-transf.ax right-unitor-inverse A B f =
  𝓓.seq (F.hom f) (𝓓.idn (F.ob B)) ＝⟨ 𝓓.idn-R _ _ _ ⟩
  F.hom f ＝⟨ 𝓓.idn-L _ _ _ ⁻¹ ⟩
  𝓓.seq (𝓓.idn (F.ob A)) (F.hom f) ∎

 abstract
  left-unitor-is-section : [𝓒,𝓓].seq left-unitor left-unitor-inverse ＝ [𝓒,𝓓].idn 1[𝓒]-F
  left-unitor-is-section =
   to-nat-transf-＝ _ _ _ _
    (dfunext fe λ A →
     𝓓.seq (𝓓.idn (F.ob A)) (𝓓.idn (F.ob A)) ＝⟨ 𝓓.idn-L _ _ _ ⟩
     𝓓.idn (F.ob A) ∎)

  left-unitor-is-retraction : [𝓒,𝓓].seq left-unitor-inverse left-unitor ＝ [𝓒,𝓓].idn F
  left-unitor-is-retraction =
   to-nat-transf-＝ _ _ _ _
    (dfunext fe λ A →
     𝓓.seq (𝓓.idn (F.ob A)) (𝓓.idn (F.ob A)) ＝⟨ 𝓓.idn-L _ _ _ ⟩
     𝓓.idn (F.ob A) ∎)

  right-unitor-is-section : [𝓒,𝓓].seq right-unitor right-unitor-inverse ＝ [𝓒,𝓓].idn F-1[𝓓]
  right-unitor-is-section =
   to-nat-transf-＝ _ _ _ _
    (dfunext fe λ A →
     𝓓.seq (𝓓.idn (F.ob A)) (𝓓.idn (F.ob A)) ＝⟨ 𝓓.idn-L _ _ _ ⟩
     𝓓.idn (F.ob A) ∎)

  right-unitor-is-retraction : [𝓒,𝓓].seq right-unitor-inverse right-unitor ＝ [𝓒,𝓓].idn F
  right-unitor-is-retraction =
   to-nat-transf-＝ _ _ _ _
    (dfunext fe λ A →
     𝓓.seq (𝓓.idn (F.ob A)) (𝓓.idn (F.ob A)) ＝⟨ 𝓓.idn-L _ _ _ ⟩
     𝓓.idn (F.ob A) ∎)


module
 _
  {𝓒 : precategory 𝓣 𝓤} {𝓓 : precategory 𝓥 𝓦}
  {𝓔 : precategory 𝓣' 𝓤'} {𝓕 : precategory 𝓥' 𝓦'}
  (open functor-of-precategories)
  (F : functor 𝓒 𝓓) (G : functor 𝓓 𝓔) (H : functor 𝓔 𝓕)
 where
 open natural-transformation

 private
  [𝓒,𝓕] = functor-category.precat 𝓒 𝓕
  module [𝓒,𝓕] = precategory [𝓒,𝓕]
  module 𝓕 = precategory 𝓕
  module H = functor H
  module G = functor G
  module F = functor F
  F-G = composite-functor.fun F G
  G-H = composite-functor.fun G H
  F-[G-H] = composite-functor.fun F G-H
  [F-G]-H = composite-functor.fun F-G H

 associator : [𝓒,𝓕].hom F-[G-H] [F-G]-H
 nat-transf.str associator A = 𝓕.idn (H.ob (G.ob (F.ob A)))
 nat-transf.ax associator A B f =
  𝓕.seq (H.hom (G.hom (F.hom f))) (𝓕.idn _) ＝⟨ 𝓕.idn-R _ _ _ ⟩
  H.hom (G.hom (F.hom f)) ＝⟨ 𝓕.idn-L _ _ _ ⁻¹ ⟩
  𝓕.seq (𝓕.idn _) (H.hom (G.hom (F.hom f))) ∎

 associator-inverse : [𝓒,𝓕].hom [F-G]-H F-[G-H]
 nat-transf.str associator-inverse A = 𝓕.idn (H.ob (G.ob (F.ob A)))
 nat-transf.ax associator-inverse A B f =
  𝓕.seq (H.hom (G.hom (F.hom f))) (𝓕.idn _) ＝⟨ 𝓕.idn-R _ _ _ ⟩
  H.hom (G.hom (F.hom f)) ＝⟨ 𝓕.idn-L _ _ _ ⁻¹ ⟩
  𝓕.seq (𝓕.idn _) (H.hom (G.hom (F.hom f))) ∎

 abstract
  associator-is-section : [𝓒,𝓕].seq associator associator-inverse ＝ [𝓒,𝓕].idn F-[G-H]
  associator-is-section =
   to-nat-transf-＝ _ _ _ _
    (dfunext fe λ A →
     𝓕.seq (𝓕.idn _) (𝓕.idn _) ＝⟨ 𝓕.idn-L _ _ _ ⟩
     𝓕.idn _ ∎)

  associator-is-retraction : [𝓒,𝓕].seq associator-inverse associator ＝ [𝓒,𝓕].idn [F-G]-H
  associator-is-retraction =
   to-nat-transf-＝ _ _ _ _
    (dfunext fe λ A →
     𝓕.seq (𝓕.idn _) (𝓕.idn _) ＝⟨ 𝓕.idn-L _ _ _ ⟩
     𝓕.idn _ ∎)

\end{code}
