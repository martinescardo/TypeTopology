Jon Sterling, started 16th Dec 2022

The upshift and downshift, when viewed in terms of the categories obtained from
the duploid, will ultimately form a pair of adjunctions `↑⊣↓` and `⇓⊣⇑`
respectively:

1. The upshift becomes a *left* adjoint functor `↑ : 𝓟-thunk → 𝓝-lin` from the
category of positive types and thunkable maps to the category of negative
objects and linear maps. Its right adjoint is the downshift `↓ : 𝓝-lin →
𝓟-thunk`.

2. The upshift becomes a *right* adjoint functor `⇑ : 𝓟 → 𝓝` from the category
of positive types and all maps to the category of negative objects and all
maps. Its left adjoint is the downshift `⇓ : 𝓝 → 𝓟`.

The category of positive objects and all maps is the Kleisli category for the
monad of the adjunction `↑⊣↓`; the category of negative objects and all maps is
the Kleisli category for the comonad of `↑⊣↓`. Then the (flipped) adjunction
`⇓⊣⇑` is the usual adjunction between the Kleisli categories for the monad and
the comonad respectively.


\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
import Duploids.Duploid

module Duploids.ShiftFunctors
 (fe : Fun-Ext)
 (pt : propositional-truncations-exist)
 where

open import UF.Base
open import UF.Retracts
open import UF.Subsingletons

open import Categories.Category fe
open import Categories.Functor fe
open import Categories.NaturalTransformation fe
open import Categories.Adjunction fe
open import Duploids.Preduploid
open import Duploids.Duploid fe pt

module _ (𝓓 : duploid 𝓤 𝓥) where
 private module 𝓓 = duploid 𝓓
 open duploid-extras 𝓓
 open duploid-notation 𝓓
 open functor-of-precategories

 open import Duploids.Categories fe pt 𝓓.underlying-preduploid

 -- TODO: move these lemmas elsewhere
 module _ {U V : _} {i : U 𝓓.⊢ U} {f : U 𝓓.⊢ V} where
  abstract
   lem-rewrite-idn-L
    : i ＝ 𝓓.idn _
    → i >> f ＝ f
   lem-rewrite-idn-L p =
    i >> f ＝⟨ ap (_>> f) p ⟩
    𝓓.idn _ >> f ＝⟨ 𝓓.idn-L _ _ _ ⟩
    f ∎

 module _ {U V : _} {i : V 𝓓.⊢ V} {f : U 𝓓.⊢ V} where
  abstract
   lem-rewrite-idn-R
    : i ＝ 𝓓.idn _
    → f >> i ＝ f
   lem-rewrite-idn-R p =
    f >> i ＝⟨ ap (f >>_) p ⟩
    f >> 𝓓.idn _ ＝⟨ 𝓓.idn-R _ _ _ ⟩
    f ∎

 module _ {U V : _} {f : U 𝓓.⊢ V} where
  abstract
   lem-𝒹[𝒻-] : 𝒹 >> (𝒻 >> f) ＝ f
   lem-𝒹[𝒻-] =
    𝒹 >> (𝒻 >> f) ＝⟨ 𝓓.delay-thunkable _ _ _ _ ⁻¹ ⟩
    (𝒹 >> 𝒻) >> f ＝⟨ lem-rewrite-idn-L (pr₂ 𝓓.force-delay-inverse) ⟩
    f ∎

   lem-[-𝓌]𝓊 : (f >> 𝓌) >> 𝓊 ＝ f
   lem-[-𝓌]𝓊 =
    (f >> 𝓌) >> 𝓊 ＝⟨ 𝓓.unwrap-linear _ _ _ _ ⟩
    f >> (𝓌 >> 𝓊) ＝⟨ lem-rewrite-idn-R (pr₁ 𝓓.wrap-unwrap-inverse) ⟩
    f ∎

   lem-𝓌[𝓊-] : 𝓌 >> (𝓊 >> f) ＝ f
   lem-𝓌[𝓊-] =
    𝓌 >> (𝓊 >> f) ＝⟨ 𝓓.wrap-thunkable _ _ _ _ ⁻¹ ⟩
    (𝓌 >> 𝓊) >> f ＝⟨ lem-rewrite-idn-L (pr₁ 𝓓.wrap-unwrap-inverse) ⟩
    f ∎

   lem-[-𝒹]𝒻 : (f >> 𝒹) >> 𝒻 ＝ f
   lem-[-𝒹]𝒻 =
    (f >> 𝒹) >> 𝒻 ＝⟨ 𝓓.force-linear _ _ _ _ ⟩
    f >> (𝒹 >> 𝒻) ＝⟨ lem-rewrite-idn-R (pr₂ 𝓓.force-delay-inverse) ⟩
    f ∎

 module _ {U V : _} {f : 𝓓.⇓ U 𝓓.⊢ V} where
  abstract
   lem-𝓊[𝓌-] : 𝓊 >> (𝓌 >> f) ＝ f
   lem-𝓊[𝓌-] =
    (𝓊 >> (𝓌 >> f)) ＝⟨ f-lin _ _ _ _ ⁻¹ ⟩
    (𝓊 >> 𝓌) >> f ＝⟨ lem-rewrite-idn-L (pr₂ 𝓓.wrap-unwrap-inverse) ⟩
    f ∎
    where
     f-lin : 𝓓.is-linear f
     f-lin = 𝓓.⇓-positive U V f


 -- forget linearity
 module ForgetLinearity where
  structure : functor-structure 𝓢 𝓝
  pr₁ structure A = A
  pr₂ structure A B f = pr₁ f

  axioms : functor-axioms 𝓢 𝓝 structure
  pr₁ axioms _ = refl
  pr₂ axioms _ _ _ _ _ = refl

  fun : functor 𝓢 𝓝
  fun = make structure axioms

 𝓢⇒𝓝 = ForgetLinearity.fun
 module 𝓢⇒𝓝 = functor 𝓢⇒𝓝

 -- forget thunkability
 module ForgetThunkability where
  structure : functor-structure 𝓒 𝓟
  pr₁ structure A = A
  pr₂ structure A B f = pr₁ f

  axioms : functor-axioms 𝓒 𝓟 structure
  pr₁ axioms _ = refl
  pr₂ axioms _ _ _ _ _ = refl

  fun : functor 𝓒 𝓟
  fun = make structure axioms

 𝓒⇒𝓟 = ForgetThunkability.fun
 module 𝓒⇒𝓟 = functor 𝓒⇒𝓟

 module Downshift where
  module str where
   ob : 𝓝.ob → 𝓒.ob
   ob (N , _) = 𝓓.⇓ N , 𝓓.⇓-positive N

   module _ (M N : 𝓝.ob) (f : 𝓝.hom M N) where
    hom-𝓟 : 𝓟.hom (ob M) (ob N)
    hom-𝓟 = 𝓊 >> (f >> 𝓌)

    hom-thunkable : 𝓓.is-thunkable hom-𝓟
    hom-thunkable U V g h =
     ((𝓊 >> (f >> 𝓌)) >> g) >> h ＝⟨ ap (_>> h) (𝓊[M]-th _ _ _ _) ⟩
     (𝓊 >> ((f >> 𝓌) >> g)) >> h ＝⟨ 𝓊[M]-th _ _ _ _ ⟩
     𝓊 >> (((f >> 𝓌) >> g) >> h) ＝⟨ ap (𝓊 >>_) lem ⟩
     𝓊 >> ((f >> 𝓌) >> (g >> h)) ＝⟨ 𝓊[M]-th _ _ _ _ ⁻¹ ⟩
     (𝓊 >> (f >> 𝓌)) >> (g >> h) ∎
     where

      f-th : 𝓓.is-thunkable f
      f-th = pr₂ N (pr₁ M) f

      g-lin : 𝓓.is-linear g
      g-lin = 𝓓.⇓-positive (pr₁ N) U g

      𝓊[M]-th : 𝓓.is-thunkable (𝓊 {pr₁ M})
      𝓊[M]-th = pr₂ M (𝓓.⇓ (pr₁ M)) 𝓊

      lem : ((f >> 𝓌) >> g) >> h ＝ (f >> 𝓌) >> (g >> h)
      lem =
       ((f >> 𝓌) >> g) >> h ＝⟨ ap (_>> h) (g-lin _ _ _ _) ⟩
       (f >> (𝓌 >> g)) >> h ＝⟨ f-th _ _ _ _ ⟩
       f >> ((𝓌 >> g) >> h) ＝⟨ ap (f >>_) (𝓓.wrap-thunkable _ _ _ _) ⟩
       f >> (𝓌 >> (g >> h)) ＝⟨ f-th _ _ _ _ ⁻¹ ⟩
       (f >> 𝓌) >> (g >> h) ∎


    hom : 𝓒.hom (ob M) (ob N)
    pr₁ hom = hom-𝓟
    pr₂ hom = hom-thunkable

   structure : functor-structure 𝓝 𝓒
   structure = ob , hom

  module ax where
   preserves-idn : statement-preserves-idn 𝓝 𝓒 str.structure
   preserves-idn M =
    PositivesAndThunkableMaps.to-hom-＝ (str.ob M) (str.ob M) _ _
     (𝓊 >> (𝓝.idn M >> 𝓌) ＝⟨ ap (𝓊 >>_) (𝓓.idn-L _ _ _) ⟩
      𝓊 >> 𝓌 ＝⟨ pr₂ 𝓓.wrap-unwrap-inverse ⟩
      𝓟.idn (str.ob M) ∎)

   preserves-seq : statement-preserves-seq 𝓝 𝓒 str.structure
   preserves-seq M N O f g =
    PositivesAndThunkableMaps.to-hom-＝ (str.ob M) (str.ob O) _ _
     (𝓊 >> ((f >> g) >> 𝓌) ＝⟨ ap (𝓊 >>_) (f-th _ _ _ _) ⟩
      𝓊 >> (f >> (g >> 𝓌)) ＝⟨ 𝓊[M]-th _ _ _ _ ⁻¹ ⟩
      (𝓊 >> f) >> (g >> 𝓌) ＝⟨ ap (_>> (g >> 𝓌)) lem1 ⟩
      ((𝓊 >> (f >> 𝓌)) >> 𝓊) >> (g >> 𝓌) ＝⟨ str.hom-thunkable M N _ _ _ _ _ ⟩
      (𝓊 >> (f >> 𝓌)) >> (𝓊 >> (g >> 𝓌)) ∎)
    where
     f-th : 𝓓.is-thunkable f
     f-th = pr₂ N (pr₁ M) f

     𝓊[M]-th : 𝓓.is-thunkable (𝓊 {pr₁ M})
     𝓊[M]-th = pr₂ M (𝓓.⇓ (pr₁ M)) 𝓊

     lem1 : (𝓊 >> f) ＝ (𝓊 >> (f >> 𝓌)) >> 𝓊
     lem1 =
      𝓊 >> f ＝⟨ ap (𝓊 >>_) (lem-[-𝓌]𝓊 ⁻¹) ⟩
      𝓊 >> ((f >> 𝓌) >> 𝓊) ＝⟨ 𝓓.unwrap-linear _ _ _ _ ⁻¹ ⟩
      ((𝓊 >> (f >> 𝓌)) >> 𝓊) ∎

   axioms : functor-axioms 𝓝 𝓒 str.structure
   pr₁ axioms = preserves-idn
   pr₂ axioms = preserves-seq

  fun : functor 𝓝 𝓒
  fun = make str.structure ax.axioms

 𝓝⇒𝓒 = Downshift.fun
 module 𝓝⇒𝓒 = functor 𝓝⇒𝓒

 module Upshift where
  module str where
   ob : 𝓟.ob → 𝓢.ob
   ob (A , A-pos) = 𝓓.⇑ A , 𝓓.⇑-negative A

   module _ (A B : 𝓟.ob) (f : 𝓟.hom A B) where
    hom-𝓝 : 𝓝.hom (ob A) (ob B)
    hom-𝓝 = 𝒻 >> (f >> 𝒹)

    hom-linear : 𝓓.is-linear hom-𝓝
    hom-linear U V g h =
     ((h >> g) >> (𝒻 >> (f >> 𝒹))) ＝⟨ hg-th _ _ _ _ ⁻¹ ⟩
     ((h >> g) >> 𝒻) >> (f >> 𝒹) ＝⟨ ap (_>> (f >> 𝒹)) (𝓓.force-linear _ _ _ _) ⟩
     (h >> (g >> 𝒻)) >> (f >> 𝒹) ＝⟨ f𝒹-lin _ _ _ _ ⟩
     (h >> ((g >> 𝒻) >> (f >> 𝒹))) ＝⟨ ap (h >>_) (g-th _ _ _ _) ⟩
     h >> (g >> (𝒻 >> (f >> 𝒹))) ∎
     where
      f𝒹-lin : 𝓓.is-linear (f >> 𝒹)
      f𝒹-lin = pr₂ A (𝓓.⇑ (pr₁ B)) (f >> 𝒹)

      g-th : 𝓓.is-thunkable g
      g-th = 𝓓.⇑-negative (pr₁ A) V g

      hg-th : 𝓓.is-thunkable (h >> g)
      hg-th = 𝓓.⇑-negative (pr₁ A) U (h >> g)

    hom : 𝓢.hom (ob A) (ob B)
    hom = hom-𝓝 , hom-linear

   structure : functor-structure 𝓟 𝓢
   structure = ob , hom

  module ax where
   private
    abstract
     preserves-idn-𝓝 : (A : 𝓟.ob) → 𝒻 {pr₁ A} >> (𝓓.idn _ >> 𝒹) ＝ 𝓓.idn _
     preserves-idn-𝓝 (A , A-pos) =
      𝒻 >> (𝓓.idn A >> 𝒹) ＝⟨ ap (𝒻 >>_) (𝓓.idn-L _ _ _) ⟩
      𝒻 >> 𝒹 ＝⟨ pr₁ 𝓓.force-delay-inverse ⟩
      𝓓.idn (𝓓.⇑ A) ∎

     preserves-seq-𝓝
      : (A B C : 𝓟.ob)
      → (f : 𝓟.hom A B)
      → (g : 𝓟.hom B C)
      → 𝒻 >> ((f >> g) >> 𝒹) ＝ (𝒻 >> (f >> 𝒹)) >> (𝒻 >> (g >> 𝒹))
     preserves-seq-𝓝 (A , A-pos) (B , B-pos) (C , C-pos) f g =
      𝒻 >> ((f >> g) >> 𝒹) ＝⟨ ap (𝒻 >>_) (𝒹-linear _ _ _ _) ⟩
      𝒻 >> (f >> (g >> 𝒹)) ＝⟨ g-𝒹-linear _ _ _ _ ⁻¹ ⟩
      ((𝒻 >> f) >> (g >> 𝒹)) ＝⟨ ap (_>> (g >> 𝒹)) (help1 ⁻¹) ⟩
      ((𝒻 >> (f >> 𝒹)) >> 𝒻) >> (g >> 𝒹) ＝⟨ g-𝒹-linear _ _ _ _ ⟩
      (𝒻 >> (f >> 𝒹)) >> (𝒻 >> (g >> 𝒹)) ∎
      where
       help1 : ((𝒻 >> (f >> 𝒹)) >> 𝒻) ＝ 𝒻 >> f
       help1 =
        ((𝒻 >> (f >> 𝒹)) >> 𝒻) ＝⟨ 𝓓.force-linear _ _ _ _ ⟩
        (𝒻 >> ((f >> 𝒹) >> 𝒻)) ＝⟨ ap (𝒻 >>_) lem-[-𝒹]𝒻 ⟩
        (𝒻 >> f) ∎

       g-𝒹-linear : 𝓓.is-linear (g >> 𝒹)
       g-𝒹-linear = B-pos (𝓓.⇑ C) (g >> 𝒹)

       𝒹-linear : 𝓓.is-linear (𝒹 {C})
       𝒹-linear = C-pos (𝓓.⇑ C) 𝒹


     preserves-idn : statement-preserves-idn 𝓟 𝓢 str.structure
     preserves-idn A =
      NegativesAndLinearMaps.to-hom-＝ (str.ob A) (str.ob A) _ _
       (preserves-idn-𝓝 A)

     preserves-seq : statement-preserves-seq 𝓟 𝓢 str.structure
     preserves-seq A B C f g =
      NegativesAndLinearMaps.to-hom-＝ (str.ob A) (str.ob C) _ _
       (preserves-seq-𝓝 A B C f g)


   axioms : functor-axioms 𝓟 𝓢 str.structure
   axioms = preserves-idn , preserves-seq

  fun : functor 𝓟 𝓢
  fun = make str.structure ax.axioms

 𝓟⇒𝓢 = Upshift.fun
 module 𝓟⇒𝓢 = functor 𝓟⇒𝓢

 [↑] : functor 𝓒 𝓢
 [↑] = composite-functor.fun 𝓒⇒𝓟 𝓟⇒𝓢

 [↓] : functor 𝓢 𝓒
 [↓] = composite-functor.fun 𝓢⇒𝓝 𝓝⇒𝓒

 [⇑] : functor 𝓟 𝓝
 [⇑] = composite-functor.fun 𝓟⇒𝓢 𝓢⇒𝓝

 [⇓] : functor 𝓝 𝓟
 [⇓] = composite-functor.fun 𝓝⇒𝓒 𝓒⇒𝓟

 [⇑-⇓] : functor 𝓟 𝓟
 [⇑-⇓] = composite-functor.fun [⇑] [⇓]

 [⇓-⇑] : functor 𝓝 𝓝
 [⇓-⇑] = composite-functor.fun [⇓] [⇑]

 1[𝓝] : functor 𝓝 𝓝
 1[𝓝] = identity-functor.fun 𝓝

 1[𝓟] : functor 𝓟 𝓟
 1[𝓟] = identity-functor.fun 𝓟


 module effectful-adjunction where
  open adjunction-of-precategories 𝓝 𝓟
  open natural-transformation

  [𝓝,𝓝] = functor-category.precat 𝓝 𝓝
  module [𝓝,𝓝] = precategory [𝓝,𝓝]

  module unit where
   str : transf _ _ 1[𝓝] [⇓-⇑]
   str M = 𝓌 >> 𝒹

   abstract
    ax : is-natural _ _ 1[𝓝] [⇓-⇑] str
    ax M N f =
     f >> (𝓌 >> 𝒹 {𝓓.⇓ (pr₁ N)}) ＝⟨ 𝒹[⇓]-linear _ _ _ _ ⁻¹ ⟩
     (f >> 𝓌) >> 𝒹 ＝⟨ ap (_>> 𝒹) lem ⟩
     ((𝓌 >> 𝒹) >> (𝒻 >> (𝓊 >> (f >> 𝓌)))) >> 𝒹 ＝⟨ 𝒹[⇓]-linear _ _ _ _ ⟩
     (𝓌 >> 𝒹) >> ((𝒻 >> (𝓊 >> (f >> 𝓌))) >> 𝒹) ＝⟨ ap ((𝓌 >> 𝒹) >>_) (𝒹[⇓]-linear _ _ _ _) ⟩
     (𝓌 >> 𝒹) >> (𝒻 >> ((𝓊 >> (f >> 𝓌)) >> 𝒹)) ∎

     where
      𝒹[⇓]-linear : {Z : _} → 𝓓.is-linear (𝒹 {𝓓.⇓ Z})
      𝒹[⇓]-linear = 𝓓.⇓-positive _ _ _

      lem : (f >> 𝓌) ＝ (𝓌 >> 𝒹) >> (𝒻 >> (𝓊 >> (f >> 𝓌)))
      lem =
       f >> 𝓌 ＝⟨ lem-𝓌[𝓊-] ⁻¹ ⟩
       𝓌 >> (𝓊 >> (f >> 𝓌)) ＝⟨ ap (𝓌 >>_) (lem-𝒹[𝒻-] ⁻¹) ⟩
       𝓌 >> (𝒹 >> (𝒻 >> (𝓊 >> (f >> 𝓌)))) ＝⟨ 𝓓.wrap-thunkable _ _ _ _ ⁻¹ ⟩
       (𝓌 >> 𝒹) >> (𝒻 >> (𝓊 >> (f >> 𝓌))) ∎

   unit : nat-transf _ _ 1[𝓝] [⇓-⇑]
   unit = make str ax

  module counit where
   str : transf _ _ [⇑-⇓] 1[𝓟]
   str P = 𝓊 >> 𝒻

   abstract
    ax : is-natural _ _ [⇑-⇓] 1[𝓟] str
    ax P Q f =
     (𝓊 >> ((𝒻 >> (f >> 𝒹)) >> 𝓌)) >> (𝓊 >> 𝒻) ＝⟨ 𝓓.force-linear _ _ _ _ ⁻¹ ⟩
     ((𝓊 >> ((𝒻 >> (f >> 𝒹)) >> 𝓌)) >> 𝓊) >> 𝒻 ＝⟨ ap (_>> 𝒻) lem1 ⟩
     (𝓊 >> (𝒻 >> (f >> 𝒹))) >> 𝒻 ＝⟨ 𝓓.force-linear _ _ _ _ ⟩
     𝓊 >> ((𝒻 >> (f >> 𝒹)) >> 𝒻) ＝⟨ ap (𝓊 >>_) lem2 ⟩
     𝓊 >> (𝒻 >> f) ＝⟨ f-lin _ _ _ _ ⁻¹ ⟩
     (𝓊 >> 𝒻) >> f ∎

     where
      f-lin : 𝓓.is-linear f
      f-lin = pr₂ P (pr₁ Q) f

      lem1 : (𝓊 >> ((𝒻 >> (f >> 𝒹)) >> 𝓌)) >> 𝓊 ＝ (𝓊 >> (𝒻 >> (f >> 𝒹)))
      lem1 =
       (𝓊 >> ((𝒻 >> (f >> 𝒹)) >> 𝓌)) >> 𝓊 ＝⟨ 𝓓.unwrap-linear _ _ _ _ ⟩
       𝓊 >> (((𝒻 >> (f >> 𝒹)) >> 𝓌) >> 𝓊) ＝⟨ ap (𝓊 >>_) lem-[-𝓌]𝓊 ⟩
       𝓊 >> (𝒻 >> (f >> 𝒹)) ∎

      lem2 : (𝒻 >> (f >> 𝒹)) >> 𝒻 ＝ 𝒻 >> f
      lem2 =
       (𝒻 >> (f >> 𝒹)) >> 𝒻 ＝⟨ 𝓓.force-linear _ _ _ _ ⟩
       𝒻 >> ((f >> 𝒹) >> 𝒻) ＝⟨ ap (𝒻 >>_) lem-[-𝒹]𝒻 ⟩
       𝒻 >> f ∎

   counit : nat-transf _ _ [⇑-⇓] 1[𝓟]
   counit = make str ax

  str : adjunction-structure [⇓] [⇑]
  pr₁ str = unit.unit
  pr₂ str = counit.counit

  abstract
   ax : adjunction-axioms [⇓] [⇑] str
   pr₁ ax =
    to-nat-transf-＝ 𝓝 𝓟 [⇓] [⇓]
     (dfunext fe λ M →
      (𝓓.idn _ >> (𝓊 >> ((𝓌 >> 𝒹) >> 𝓌))) >> ((𝓓.idn _) >> ((𝓊 >> 𝒻) >> 𝓓.idn _))
       ＝⟨ ap (_>> (𝓓.idn _ >> ((𝓊 >> 𝒻) >> 𝓓.idn _))) (𝓓.idn-L _ _ _) ⟩
      (𝓊 >> ((𝓌 >> 𝒹) >> 𝓌)) >> ((𝓓.idn _) >> ((𝓊 >> 𝒻) >> 𝓓.idn _))
       ＝⟨ ap ((𝓊 >> ((𝓌 >> 𝒹) >> 𝓌)) >>_) lem1 ⟩
      (𝓊 >> ((𝓌 >> 𝒹) >> 𝓌)) >> (𝓊 >> 𝒻)
       ＝⟨ 𝓓.force-linear _ _ _ _ ⁻¹ ⟩
      ((𝓊 >> ((𝓌 >> 𝒹) >> 𝓌)) >> 𝓊) >> 𝒻
       ＝⟨ ap (_>> 𝒻) lem0 ⟩
      𝒹 >> 𝒻
       ＝⟨ pr₂ 𝓓.force-delay-inverse ⟩
      𝓓.idn _ ∎)

    where
     lem0 : {A : _} → (𝓊 {A} >> ((𝓌 >> 𝒹) >> 𝓌)) >> 𝓊 ＝ 𝒹
     lem0 =
      (𝓊 >> ((𝓌 >> 𝒹) >> 𝓌)) >> 𝓊 ＝⟨ 𝓓.unwrap-linear _ _ _ _ ⟩
      (𝓊 >> (((𝓌 >> 𝒹) >> 𝓌) >> 𝓊)) ＝⟨ ap (𝓊 >>_) lem-[-𝓌]𝓊 ⟩
      (𝓊 >> (𝓌 >> 𝒹)) ＝⟨ lem-𝓊[𝓌-] ⟩
      𝒹 ∎

     lem1 : {A B : _} {f : A 𝓓.⊢ B} → (𝓓.idn _ >> (f >> 𝓓.idn _)) ＝ f
     lem1 =
      𝓓.idn _ >> (_ >> 𝓓.idn _) ＝⟨ 𝓓.idn-L _ _ _ ⟩
      _ >> 𝓓.idn _ ＝⟨ 𝓓.idn-R _ _ _ ⟩
      _ ∎

   pr₂ ax =
    to-nat-transf-＝ 𝓟 𝓝 [⇑] [⇑]
     (dfunext fe λ P →
      (𝓓.idn _ >> (𝓌 >> 𝒹)) >> (𝓓.idn _ >> ((𝒻 >> ((𝓊 >> 𝒻) >> 𝒹)) >> 𝓓.idn _))
       ＝⟨ ap (_>> (𝓓.idn _ >> ((𝒻 >> ((𝓊 >> 𝒻) >> 𝒹)) >> 𝓓.idn _))) (𝓓.idn-L _ _ _) ⟩
      (𝓌 >> 𝒹) >> (𝓓.idn _ >> ((𝒻 >> ((𝓊 >> 𝒻) >> 𝒹)) >> 𝓓.idn _))
       ＝⟨ ap ((𝓌 >> 𝒹) >>_) (lem0 ((𝓊 >> 𝒻) >> 𝒹)) ⟩
      (𝓌 >> 𝒹) >> (𝒻 >> ((𝓊 >> 𝒻) >> 𝒹))
       ＝⟨ 𝓓.wrap-thunkable _ _ _ _ ⟩
      𝓌 >> (𝒹 >> (𝒻 >> ((𝓊 >> 𝒻) >> 𝒹)))
       ＝⟨ ap (𝓌 >>_) lem-𝒹[𝒻-] ⟩
      𝓌 >> ((𝓊 >> 𝒻) >> 𝒹)
       ＝⟨ 𝓓.wrap-thunkable _ _ _ _ ⁻¹ ⟩
      (𝓌 >> (𝓊 >> 𝒻)) >> 𝒹
       ＝⟨ ap (_>> 𝒹) lem-𝓌[𝓊-] ⟩
      𝒻 >> 𝒹
       ＝⟨ pr₁ 𝓓.force-delay-inverse ⟩
      𝓓.idn _ ∎ )
    where
     lem0
      : {U V : _} (f : 𝓓.⇓ (𝓓.⇑ U) 𝓓.⊢ V)
      → (𝓓.idn _ >> ((𝒻 >> f) >> 𝓓.idn _)) ＝ (𝒻 >> f)
     lem0 f =
      𝓓.idn _ >> ((𝒻 >> f) >> 𝓓.idn _)
       ＝⟨ 𝓓.idn-L _ _ _ ⟩
      (𝒻 >> f) >> 𝓓.idn _
       ＝⟨ 𝓓.idn-R _ _ _ ⟩
      𝒻 >> f ∎

  adj : adjunction [⇓] [⇑]
  adj = make str ax

\end{code}
