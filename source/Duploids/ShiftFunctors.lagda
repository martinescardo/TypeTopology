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
 (𝓓 : Duploids.Duploid.duploid fe pt 𝓤 𝓥)
 where

open import UF.Base
open import UF.Retracts
open import UF.Subsingletons

open import Categories.Category fe
open import Categories.Functor fe
open import Categories.NaturalTransformation fe
open import Categories.Adjunction fe
open import Duploids.Preduploid
open Duploids.Duploid fe pt

private module 𝓓 = duploid 𝓓
open duploid-extras 𝓓
open duploid-notation 𝓓
open functor-of-precategories

open import Duploids.Categories fe pt 𝓓.underlying-preduploid

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
  ob (N , N-neg) = 𝓓.⇓ N N-neg , 𝓓.⇓-positive N N-neg

  module _ (M N : 𝓝.ob) (f : 𝓝.hom M N) where
   hom-𝓟 : 𝓟.hom (ob M) (ob N)
   hom-𝓟 = 𝓊 _ >> (f >> 𝓌 _)

   hom-thunkable : 𝓓.is-thunkable hom-𝓟
   hom-thunkable U V g h =
    ((𝓊 _ >> (f >> 𝓌 _)) >> g) >> h ＝⟨ ap (_>> h) (𝓊[M]-th _ _ _ _) ⟩
    (𝓊 _ >> ((f >> 𝓌 _) >> g)) >> h ＝⟨ 𝓊[M]-th _ _ _ _ ⟩
    𝓊 _ >> (((f >> 𝓌 _) >> g) >> h) ＝⟨ ap (𝓊 _ >>_) lem ⟩
    𝓊 _ >> ((f >> 𝓌 _) >> (g >> h)) ＝⟨ 𝓊[M]-th _ _ _ _ ⁻¹ ⟩
    (𝓊 _ >> (f >> 𝓌 _)) >> (g >> h) ∎
    where

     f-th : 𝓓.is-thunkable f
     f-th = pr₂ N (pr₁ M) f

     g-lin : 𝓓.is-linear g
     g-lin = 𝓓.⇓-positive (pr₁ N) (pr₂ N) U g

     𝓊[M]-th : 𝓓.is-thunkable (𝓊 {pr₁ M} (pr₂ M))
     𝓊[M]-th = pr₂ M (𝓓.⇓ (pr₁ M) (pr₂ M)) (𝓊 _)

     lem : ((f >> 𝓌 (pr₂ N)) >> g) >> h ＝ (f >> 𝓌 (pr₂ N)) >> (g >> h)
     lem =
      ((f >> 𝓌 _) >> g) >> h ＝⟨ ap (_>> h) (g-lin _ _ _ _) ⟩
      (f >> (𝓌 _ >> g)) >> h ＝⟨ f-th _ _ _ _ ⟩
      f >> ((𝓌 _ >> g) >> h) ＝⟨ ap (f >>_) (𝓓.wrap-thunkable _ _ _ _) ⟩
      f >> (𝓌 _ >> (g >> h)) ＝⟨ f-th _ _ _ _ ⁻¹ ⟩
      (f >> 𝓌 _) >> (g >> h) ∎


   hom : 𝓒.hom (ob M) (ob N)
   pr₁ hom = hom-𝓟
   pr₂ hom = hom-thunkable

  structure : functor-structure 𝓝 𝓒
  structure = ob , hom

 module ax where
  preserves-idn : statement-preserves-idn 𝓝 𝓒 str.structure
  preserves-idn M =
   PositivesAndThunkableMaps.to-hom-＝ (str.ob M) (str.ob M) _ _
    (𝓊 _ >> (𝓝.idn M >> 𝓌 _) ＝⟨ ap (𝓊 _ >>_) (𝓓.idn-L _ _ _) ⟩
     𝓊 _ >> 𝓌 _ ＝⟨ pr₂ 𝓓.wrap-unwrap-inverse ⟩
     𝓟.idn (str.ob M) ∎)

  preserves-seq : statement-preserves-seq 𝓝 𝓒 str.structure
  preserves-seq M N O f g =
   PositivesAndThunkableMaps.to-hom-＝ (str.ob M) (str.ob O) _ _
    (𝓊 _ >> ((f >> g) >> 𝓌 _) ＝⟨ ap (𝓊 _ >>_) (f-th _ _ _ _) ⟩
     𝓊 _ >> (f >> (g >> 𝓌 _)) ＝⟨ 𝓊[M]-th _ _ _ _ ⁻¹ ⟩
     (𝓊 _ >> f) >> (g >> 𝓌 _) ＝⟨ ap (_>> (g >> 𝓌 _)) lem1 ⟩
     ((𝓊 _ >> (f >> 𝓌 _)) >> 𝓊 _) >> (g >> 𝓌 _) ＝⟨ str.hom-thunkable M N _ _ _ _ _ ⟩
     (𝓊 _ >> (f >> 𝓌 _)) >> (𝓊 _ >> (g >> 𝓌 _)) ∎)
   where
    f-th : 𝓓.is-thunkable f
    f-th = pr₂ N (pr₁ M) f

    𝓊[M]-th : 𝓓.is-thunkable (𝓊 {pr₁ M} (pr₂ M))
    𝓊[M]-th = pr₂ M (𝓓.⇓ (pr₁ M) (pr₂ M)) (𝓊 (pr₂ M))

    lem1 : (𝓊 (pr₂ M) >> f) ＝ (𝓊 (pr₂ M) >> (f >> 𝓌 (pr₂ N))) >> 𝓊 (pr₂ N)
    lem1 =
     𝓊 _ >> f ＝⟨ ap (𝓊 _ >>_) (lem-[-𝓌]𝓊 ⁻¹) ⟩
     𝓊 _ >> ((f >> 𝓌 _) >> 𝓊 _) ＝⟨ 𝓓.unwrap-linear _ _ _ _ ⁻¹ ⟩
     ((𝓊 _ >> (f >> 𝓌 _)) >> 𝓊 _) ∎

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
  ob (A , A-pos) = 𝓓.⇑ A A-pos , 𝓓.⇑-negative A A-pos

  module _ (A B : 𝓟.ob) (f : 𝓟.hom A B) where
   hom-𝓝 : 𝓝.hom (ob A) (ob B)
   hom-𝓝 = 𝒻 _ >> (f >> 𝒹 _)

   hom-linear : 𝓓.is-linear hom-𝓝
   hom-linear U V g h =
    ((h >> g) >> (𝒻 _ >> (f >> 𝒹 _))) ＝⟨ hg-th _ _ _ _ ⁻¹ ⟩
    ((h >> g) >> 𝒻 _) >> (f >> 𝒹 _) ＝⟨ ap (_>> (f >> 𝒹 _)) (𝓓.force-linear _ _ _ _) ⟩
    (h >> (g >> 𝒻 _)) >> (f >> 𝒹 _) ＝⟨ f𝒹-lin _ _ _ _ ⟩
    (h >> ((g >> 𝒻 _) >> (f >> 𝒹 _))) ＝⟨ ap (h >>_) (g-th _ _ _ _) ⟩
    h >> (g >> (𝒻 _ >> (f >> 𝒹 _))) ∎
    where
     f𝒹-lin : 𝓓.is-linear (f >> 𝒹 _)
     f𝒹-lin = pr₂ A (𝓓.⇑ (pr₁ B) (pr₂ B)) (f >> 𝒹 (pr₂ B))

     g-th : 𝓓.is-thunkable g
     g-th = 𝓓.⇑-negative (pr₁ A) (pr₂ A) V g

     hg-th : 𝓓.is-thunkable (h >> g)
     hg-th = 𝓓.⇑-negative (pr₁ A) (pr₂ A) U (h >> g)

   hom : 𝓢.hom (ob A) (ob B)
   hom = hom-𝓝 , hom-linear

  structure : functor-structure 𝓟 𝓢
  structure = ob , hom

 module ax where
  private
   abstract
    preserves-idn-𝓝 : (A : 𝓟.ob) → 𝒻 (pr₂ A) >> (𝓓.idn _ >> 𝒹 (pr₂ A)) ＝ 𝓓.idn _
    preserves-idn-𝓝 (A , A-pos) =
     𝒻 _ >> (𝓓.idn A >> 𝒹 _) ＝⟨ ap (𝒻 _ >>_) (𝓓.idn-L _ _ _) ⟩
     𝒻 _ >> 𝒹 _ ＝⟨ pr₁ 𝓓.force-delay-inverse ⟩
     𝓓.idn (𝓓.⇑ A _) ∎

    preserves-seq-𝓝
     : (A B C : 𝓟.ob)
     → (f : 𝓟.hom A B)
     → (g : 𝓟.hom B C)
     → 𝒻 (pr₂ A) >> ((f >> g) >> 𝒹 (pr₂ C))
        ＝ (𝒻 _ >> (f >> 𝒹 (pr₂ B))) >> (𝒻 (pr₂ B) >> (g >> 𝒹 (pr₂ C)))
    preserves-seq-𝓝 (A , A-pos) (B , B-pos) (C , C-pos) f g =
     𝒻 A-pos >> ((f >> g) >> 𝒹 _) ＝⟨ ap (𝒻 _ >>_) (𝒹-linear _ _ _ _) ⟩
     𝒻 A-pos >> (f >> (g >> 𝒹 _)) ＝⟨ g-𝒹-linear _ _ _ _ ⁻¹ ⟩
     ((𝒻 _ >> f) >> (g >> 𝒹 _)) ＝⟨ ap (_>> (g >> 𝒹 _)) (help1 ⁻¹) ⟩
     ((𝒻 _ >> (f >> 𝒹 _)) >> 𝒻 _) >> (g >> 𝒹 _) ＝⟨ g-𝒹-linear _ _ _ _ ⟩
     (𝒻 _ >> (f >> 𝒹 _)) >> (𝒻 _ >> (g >> 𝒹 _)) ∎
     where
      help1 : ((𝒻 A-pos >> (f >> 𝒹 B-pos)) >> 𝒻 B-pos) ＝ 𝒻 A-pos >> f
      help1 =
       ((𝒻 _ >> (f >> 𝒹 _)) >> 𝒻 _) ＝⟨ 𝓓.force-linear _ _ _ _ ⟩
       (𝒻 _ >> ((f >> 𝒹 _) >> 𝒻 _)) ＝⟨ ap (𝒻 _ >>_) lem-[-𝒹]𝒻 ⟩
       (𝒻 _ >> f) ∎

      g-𝒹-linear : 𝓓.is-linear (g >> 𝒹 C-pos)
      g-𝒹-linear = B-pos (𝓓.⇑ C C-pos) (g >> 𝒹 _)

      𝒹-linear : 𝓓.is-linear (𝒹 C-pos)
      𝒹-linear = C-pos (𝓓.⇑ C _) (𝒹 _)


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

\end{code}
